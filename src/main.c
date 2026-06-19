#include <ctype.h>
#include <errno.h>
#include <limits.h>
#include <pthread.h>
#include <signal.h>
#include <sodium.h>
#include <sqlite3.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <time.h>
#include <unistd.h>

#include <jansson.h>
#include <microhttpd.h>

#include "docs/docs_ui.h"
#include "http/response.h"
#include "http/routes_meta.h"

#define DEFAULT_PORT 8080
#define DEFAULT_DB_PATH "./data/app.db"
#define DEFAULT_KEY_FILE "./data/user_key.b64"
#define DEFAULT_SESSION_TTL_HOURS 12
#define DEFAULT_ADMIN_USERNAME "admin"
#define DEFAULT_ADMIN_PASSWORD "Admin@123456"

#define MAX_BODY_SIZE (1024 * 1024)
#define RAW_TOKEN_BYTES 32
#define TOKEN_HASH_HEX_LEN (crypto_generichash_BYTES * 2)

typedef struct {
    int port;
    int session_ttl_hours;
    const char *db_path;
    const char *key_file;
} ServerConfig;

typedef struct {
    int user_id;
    char username[128];
    char role[32];
} AuthUser;

static ServerConfig g_cfg;
static sqlite3 *g_db = NULL;
static pthread_mutex_t g_db_mutex = PTHREAD_MUTEX_INITIALIZER;
static unsigned char g_user_key[crypto_secretbox_KEYBYTES];
static volatile sig_atomic_t g_running = 1;

static void handle_signal(int sig) {
    (void)sig;
    g_running = 0;
}

static char *dup_cstr(const char *src) {
    if (src == NULL) {
        return NULL;
    }
    const size_t len = strlen(src);
    char *dst = (char *)malloc(len + 1);
    if (dst == NULL) {
        return NULL;
    }
    memcpy(dst, src, len + 1);
    return dst;
}

static int env_to_int(const char *name, int fallback) {
    const char *v = getenv(name);
    if (v == NULL || *v == '\0') {
        return fallback;
    }

    char *end = NULL;
    errno = 0;
    long n = strtol(v, &end, 10);
    if (errno != 0 || end == v || *end != '\0' || n <= 0 || n > INT_MAX) {
        return fallback;
    }
    return (int)n;
}

static void bytes_to_hex(const unsigned char *in, size_t in_len, char *out) {
    static const char hex[] = "0123456789abcdef";
    for (size_t i = 0; i < in_len; ++i) {
        out[i * 2] = hex[(in[i] >> 4) & 0x0F];
        out[i * 2 + 1] = hex[in[i] & 0x0F];
    }
    out[in_len * 2] = '\0';
}

static int hash_token(const char *token, char out_hex[TOKEN_HASH_HEX_LEN + 1]) {
    unsigned char hash[crypto_generichash_BYTES];
    if (crypto_generichash(hash, sizeof(hash), (const unsigned char *)token,
                           strlen(token), NULL, 0) != 0) {
        return -1;
    }
    bytes_to_hex(hash, sizeof(hash), out_hex);
    return 0;
}

static int generate_access_token(char *out, size_t out_size) {
    const size_t needed =
        sodium_base64_encoded_len(RAW_TOKEN_BYTES,
                                  sodium_base64_VARIANT_URLSAFE_NO_PADDING);
    if (out_size < needed) {
        return -1;
    }

    unsigned char raw[RAW_TOKEN_BYTES];
    randombytes_buf(raw, sizeof(raw));
    sodium_bin2base64(out, out_size, raw, sizeof(raw),
                      sodium_base64_VARIANT_URLSAFE_NO_PADDING);
    return 0;
}

static time_t now_epoch(void) { return time(NULL); }

static int ensure_parent_dir(const char *path) {
    if (path == NULL) {
        return -1;
    }

    char *copy = dup_cstr(path);
    if (copy == NULL) {
        return -1;
    }

    for (char *p = copy + 1; *p != '\0'; ++p) {
        if (*p == '/') {
            *p = '\0';
            if (mkdir(copy, 0755) != 0 && errno != EEXIST) {
                free(copy);
                return -1;
            }
            *p = '/';
        }
    }

    free(copy);
    return 0;
}

static int load_or_create_key(void) {
    const char *env_key = getenv("USER_DATA_KEY_B64");
    if (env_key != NULL && *env_key != '\0') {
        size_t bin_len = 0;
        if (sodium_base642bin(g_user_key, sizeof(g_user_key), env_key,
                              strlen(env_key), NULL, &bin_len, NULL,
                              sodium_base64_VARIANT_ORIGINAL) == 0 &&
            bin_len == sizeof(g_user_key)) {
            return 0;
        }
        fprintf(stderr,
                "[WARN] USER_DATA_KEY_B64 无效，将尝试从密钥文件加载。\n");
    }

    FILE *f = fopen(g_cfg.key_file, "rb");
    if (f != NULL) {
        char line[256];
        if (fgets(line, sizeof(line), f) != NULL) {
            line[strcspn(line, "\r\n")] = '\0';
            size_t bin_len = 0;
            if (sodium_base642bin(g_user_key, sizeof(g_user_key), line,
                                  strlen(line), NULL, &bin_len, NULL,
                                  sodium_base64_VARIANT_ORIGINAL) == 0 &&
                bin_len == sizeof(g_user_key)) {
                fclose(f);
                return 0;
            }
        }
        fclose(f);
    }

    randombytes_buf(g_user_key, sizeof(g_user_key));
    const size_t enc_len = sodium_base64_encoded_len(
        sizeof(g_user_key), sodium_base64_VARIANT_ORIGINAL);
    char *b64 = (char *)malloc(enc_len + 2);
    if (b64 == NULL) {
        return -1;
    }

    sodium_bin2base64(b64, enc_len + 2, g_user_key, sizeof(g_user_key),
                      sodium_base64_VARIANT_ORIGINAL);

    if (ensure_parent_dir(g_cfg.key_file) != 0) {
        free(b64);
        return -1;
    }

    f = fopen(g_cfg.key_file, "wb");
    if (f == NULL) {
        free(b64);
        return -1;
    }

    fprintf(f, "%s\n", b64);
    fclose(f);
    chmod(g_cfg.key_file, 0600);
    free(b64);

    fprintf(stdout,
            "[INFO] 已自动生成新的用户字段加密密钥: %s\n"
            "[INFO] 请妥善备份该文件，丢失后将无法解密已有用户信息。\n",
            g_cfg.key_file);

    return 0;
}

static int encrypt_text(const char *plain, char **out_b64) {
    if (plain == NULL) {
        plain = "";
    }

    const size_t plain_len = strlen(plain);
    const size_t boxed_len = crypto_secretbox_NONCEBYTES +
                             crypto_secretbox_MACBYTES + plain_len;

    unsigned char *boxed = (unsigned char *)malloc(boxed_len);
    if (boxed == NULL) {
        return -1;
    }

    unsigned char *nonce = boxed;
    unsigned char *cipher = boxed + crypto_secretbox_NONCEBYTES;
    randombytes_buf(nonce, crypto_secretbox_NONCEBYTES);

    if (crypto_secretbox_easy(cipher, (const unsigned char *)plain, plain_len,
                              nonce, g_user_key) != 0) {
        free(boxed);
        return -1;
    }

    const size_t enc_len =
        sodium_base64_encoded_len(boxed_len, sodium_base64_VARIANT_ORIGINAL);
    char *b64 = (char *)malloc(enc_len + 1);
    if (b64 == NULL) {
        free(boxed);
        return -1;
    }

    sodium_bin2base64(b64, enc_len + 1, boxed, boxed_len,
                      sodium_base64_VARIANT_ORIGINAL);

    free(boxed);
    *out_b64 = b64;
    return 0;
}

static int decrypt_text(const char *b64, char **out_plain) {
    if (b64 == NULL || *b64 == '\0') {
        *out_plain = dup_cstr("");
        return *out_plain == NULL ? -1 : 0;
    }

    const size_t max_len = strlen(b64) * 3 / 4 + 4;
    unsigned char *boxed = (unsigned char *)malloc(max_len);
    if (boxed == NULL) {
        return -1;
    }

    size_t boxed_len = 0;
    if (sodium_base642bin(boxed, max_len, b64, strlen(b64), NULL, &boxed_len,
                          NULL, sodium_base64_VARIANT_ORIGINAL) != 0) {
        free(boxed);
        return -1;
    }

    if (boxed_len <
        crypto_secretbox_NONCEBYTES + crypto_secretbox_MACBYTES) {
        free(boxed);
        return -1;
    }

    const unsigned char *nonce = boxed;
    const unsigned char *cipher = boxed + crypto_secretbox_NONCEBYTES;
    const size_t cipher_len = boxed_len - crypto_secretbox_NONCEBYTES;
    const size_t plain_len = cipher_len - crypto_secretbox_MACBYTES;

    unsigned char *plain = (unsigned char *)malloc(plain_len + 1);
    if (plain == NULL) {
        free(boxed);
        return -1;
    }

    if (crypto_secretbox_open_easy(plain, cipher, cipher_len, nonce,
                                   g_user_key) != 0) {
        free(boxed);
        free(plain);
        return -1;
    }

    plain[plain_len] = '\0';
    free(boxed);
    *out_plain = (char *)plain;
    return 0;
}

static int db_exec(const char *sql) {
    char *err = NULL;
    const int rc = sqlite3_exec(g_db, sql, NULL, NULL, &err);
    if (rc != SQLITE_OK) {
        if (err != NULL) {
            fprintf(stderr, "[DB] SQL执行失败: %s\n", err);
            sqlite3_free(err);
        }
        return -1;
    }
    return 0;
}

static int db_init(void) {
    if (ensure_parent_dir(g_cfg.db_path) != 0) {
        fprintf(stderr, "[DB] 无法创建数据库目录: %s\n", g_cfg.db_path);
        return -1;
    }

    if (sqlite3_open_v2(g_cfg.db_path, &g_db,
                        SQLITE_OPEN_READWRITE | SQLITE_OPEN_CREATE |
                            SQLITE_OPEN_FULLMUTEX,
                        NULL) != SQLITE_OK) {
        fprintf(stderr, "[DB] 打开数据库失败: %s\n", sqlite3_errmsg(g_db));
        return -1;
    }

    sqlite3_busy_timeout(g_db, 5000);

    const char *schema_sql =
        "PRAGMA foreign_keys = ON;"
        "PRAGMA journal_mode = WAL;"
        "PRAGMA synchronous = NORMAL;"

        "CREATE TABLE IF NOT EXISTS users ("
        "  id INTEGER PRIMARY KEY AUTOINCREMENT,"
        "  username TEXT NOT NULL UNIQUE,"
        "  password_hash TEXT NOT NULL,"
        "  role TEXT NOT NULL CHECK(role IN ('admin','staff')),"
        "  full_name_enc TEXT,"
        "  email_enc TEXT,"
        "  phone_enc TEXT,"
        "  created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP"
        ");"

        "CREATE TABLE IF NOT EXISTS sessions ("
        "  id INTEGER PRIMARY KEY AUTOINCREMENT,"
        "  user_id INTEGER NOT NULL,"
        "  token_hash TEXT NOT NULL UNIQUE,"
        "  expires_at INTEGER NOT NULL,"
        "  created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,"
        "  FOREIGN KEY(user_id) REFERENCES users(id) ON DELETE CASCADE"
        ");"

        "CREATE TABLE IF NOT EXISTS products ("
        "  id INTEGER PRIMARY KEY AUTOINCREMENT,"
        "  sku TEXT NOT NULL UNIQUE,"
        "  name TEXT NOT NULL,"
        "  unit TEXT NOT NULL DEFAULT '瓶',"
        "  stock_quantity INTEGER NOT NULL DEFAULT 0 CHECK(stock_quantity >= 0),"
        "  created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,"
        "  updated_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP"
        ");"

        "CREATE TABLE IF NOT EXISTS stock_movements ("
        "  id INTEGER PRIMARY KEY AUTOINCREMENT,"
        "  product_id INTEGER NOT NULL,"
        "  movement_type TEXT NOT NULL CHECK(movement_type IN ('IN','OUT')),"
        "  quantity INTEGER NOT NULL CHECK(quantity > 0),"
        "  unit_price_cents INTEGER NOT NULL CHECK(unit_price_cents >= 0),"
        "  note TEXT,"
        "  operator_user_id INTEGER NOT NULL,"
        "  created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,"
        "  FOREIGN KEY(product_id) REFERENCES products(id),"
        "  FOREIGN KEY(operator_user_id) REFERENCES users(id)"
        ");"

        "CREATE TABLE IF NOT EXISTS suppliers ("
        "  id INTEGER PRIMARY KEY AUTOINCREMENT,"
        "  name TEXT NOT NULL UNIQUE,"
        "  contact_name TEXT,"
        "  contact_phone TEXT,"
        "  created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP"
        ");"

        "CREATE TABLE IF NOT EXISTS cabinets ("
        "  id INTEGER PRIMARY KEY AUTOINCREMENT,"
        "  cabinet_code TEXT NOT NULL UNIQUE,"
        "  name TEXT NOT NULL,"
        "  location TEXT,"
        "  status TEXT NOT NULL DEFAULT 'active' CHECK(status IN ('active','inactive')),"
        "  created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP"
        ");"

        "CREATE TABLE IF NOT EXISTS product_batches ("
        "  id INTEGER PRIMARY KEY AUTOINCREMENT,"
        "  product_id INTEGER NOT NULL,"
        "  batch_no TEXT NOT NULL UNIQUE,"
        "  supplier_id INTEGER NOT NULL,"
        "  production_date TEXT NOT NULL,"
        "  arrival_quantity INTEGER NOT NULL CHECK(arrival_quantity > 0),"
        "  expiry_date TEXT NOT NULL,"
        "  note TEXT,"
        "  created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,"
        "  FOREIGN KEY(product_id) REFERENCES products(id),"
        "  FOREIGN KEY(supplier_id) REFERENCES suppliers(id)"
        ");"

        "CREATE TABLE IF NOT EXISTS cabinet_batch_stock ("
        "  cabinet_id INTEGER NOT NULL,"
        "  batch_id INTEGER NOT NULL,"
        "  current_quantity INTEGER NOT NULL DEFAULT 0 CHECK(current_quantity >= 0),"
        "  created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,"
        "  updated_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,"
        "  PRIMARY KEY (cabinet_id, batch_id),"
        "  FOREIGN KEY(cabinet_id) REFERENCES cabinets(id),"
        "  FOREIGN KEY(batch_id) REFERENCES product_batches(id)"
        ");"

        "CREATE TABLE IF NOT EXISTS sales_orders ("
        "  id INTEGER PRIMARY KEY AUTOINCREMENT,"
        "  order_no TEXT NOT NULL UNIQUE,"
        "  cabinet_id INTEGER NOT NULL,"
        "  batch_id INTEGER NOT NULL,"
        "  product_id INTEGER NOT NULL,"
        "  quantity INTEGER NOT NULL CHECK(quantity > 0),"
        "  unit_price_cents INTEGER NOT NULL CHECK(unit_price_cents >= 0),"
        "  total_price_cents INTEGER NOT NULL CHECK(total_price_cents >= 0),"
        "  note TEXT,"
        "  created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,"
        "  FOREIGN KEY(cabinet_id) REFERENCES cabinets(id),"
        "  FOREIGN KEY(batch_id) REFERENCES product_batches(id),"
        "  FOREIGN KEY(product_id) REFERENCES products(id)"
        ");"

        "CREATE INDEX IF NOT EXISTS idx_sessions_token_hash ON sessions(token_hash);"
        "CREATE INDEX IF NOT EXISTS idx_sessions_expires_at ON sessions(expires_at);"
        "CREATE INDEX IF NOT EXISTS idx_products_sku ON products(sku);"
        "CREATE INDEX IF NOT EXISTS idx_movements_product_id ON "
        "stock_movements(product_id);"
        "CREATE INDEX IF NOT EXISTS idx_movements_created_at ON "
        "stock_movements(created_at);"
        "CREATE INDEX IF NOT EXISTS idx_batches_product_id ON product_batches(product_id);"
        "CREATE INDEX IF NOT EXISTS idx_batches_supplier_id ON product_batches(supplier_id);"
        "CREATE INDEX IF NOT EXISTS idx_batches_production_date ON product_batches(production_date);"
        "CREATE INDEX IF NOT EXISTS idx_cabinet_stock_cabinet_id ON cabinet_batch_stock(cabinet_id);"
        "CREATE INDEX IF NOT EXISTS idx_cabinet_stock_batch_id ON cabinet_batch_stock(batch_id);"
        "CREATE INDEX IF NOT EXISTS idx_orders_cabinet_id ON sales_orders(cabinet_id);"
        "CREATE INDEX IF NOT EXISTS idx_orders_batch_id ON sales_orders(batch_id);"
        "CREATE INDEX IF NOT EXISTS idx_orders_created_at ON sales_orders(created_at);"

        "INSERT OR IGNORE INTO products (sku, name, unit, stock_quantity) VALUES "
        "('SEED-WATER-550', '系统示例矿泉水550ml', '瓶', 50);"

        "INSERT OR IGNORE INTO suppliers (name, contact_name, contact_phone) VALUES "
        "('示例水厂', '张经理', '13800000001');"

        "INSERT OR IGNORE INTO cabinets (cabinet_code, name, location, status) VALUES "
        "('CAB-001', '东门柜机', '园区东门入口', 'active'),"
        "('CAB-002', '办公楼柜机', 'A座办公楼一楼', 'active');";

    if (db_exec(schema_sql) != 0) {
        return -1;
    }

    return 0;
}

static int append_body(ConnectionInfo *ci, const char *data, size_t size) {
    if (size == 0) {
        return 0;
    }
    if (ci->body_size + size > MAX_BODY_SIZE) {
        return -1;
    }

    char *new_buf = (char *)realloc(ci->body, ci->body_size + size + 1);
    if (new_buf == NULL) {
        return -1;
    }

    ci->body = new_buf;
    memcpy(ci->body + ci->body_size, data, size);
    ci->body_size += size;
    ci->body[ci->body_size] = '\0';
    return 0;
}

static int is_method_with_body(const char *method) {
    return strcmp(method, MHD_HTTP_METHOD_POST) == 0 ||
           strcmp(method, MHD_HTTP_METHOD_PUT) == 0 ||
           strcmp(method, MHD_HTTP_METHOD_PATCH) == 0;
}

static int parse_json_body(ConnectionInfo *ci, json_t **out,
                           char err_msg[256]) {
    if (ci->body_size == 0) {
        snprintf(err_msg, 256, "请求体不能为空");
        return -1;
    }

    json_error_t jerr;
    json_t *obj = json_loadb(ci->body, ci->body_size, 0, &jerr);
    if (obj == NULL || !json_is_object(obj)) {
        if (obj != NULL) {
            json_decref(obj);
        }
        snprintf(err_msg, 256, "JSON 格式错误: %s", jerr.text);
        return -1;
    }

    *out = obj;
    return 0;
}

static const char *safe_col_text(sqlite3_stmt *stmt, int col) {
    const unsigned char *text = sqlite3_column_text(stmt, col);
    return text == NULL ? "" : (const char *)text;
}

static int db_user_count(int *count_out) {
    sqlite3_stmt *stmt = NULL;
    int rc = sqlite3_prepare_v2(g_db, "SELECT COUNT(*) FROM users;", -1, &stmt, NULL);
    if (rc != SQLITE_OK) {
        return -1;
    }

    rc = sqlite3_step(stmt);
    if (rc != SQLITE_ROW) {
        sqlite3_finalize(stmt);
        return -1;
    }

    *count_out = sqlite3_column_int(stmt, 0);
    sqlite3_finalize(stmt);
    return 0;
}

static int ensure_default_admin_user(void) {
    int user_count = 0;
    if (db_user_count(&user_count) != 0) {
        fprintf(stderr, "[DB] 查询用户数量失败，无法初始化默认管理员\n");
        return -1;
    }
    if (user_count > 0) {
        return 0;
    }

    const char *admin_username = getenv("DEFAULT_ADMIN_USERNAME");
    if (admin_username == NULL || *admin_username == '\0') {
        admin_username = DEFAULT_ADMIN_USERNAME;
    }

    const char *admin_password = getenv("DEFAULT_ADMIN_PASSWORD");
    if (admin_password == NULL || *admin_password == '\0') {
        admin_password = DEFAULT_ADMIN_PASSWORD;
    }

    char password_hash[crypto_pwhash_STRBYTES];
    if (crypto_pwhash_str(password_hash, admin_password, strlen(admin_password),
                          crypto_pwhash_OPSLIMIT_INTERACTIVE,
                          crypto_pwhash_MEMLIMIT_INTERACTIVE) != 0) {
        fprintf(stderr, "[SECURITY] 默认管理员密码哈希失败\n");
        return -1;
    }

    char *full_name_enc = NULL;
    char *email_enc = NULL;
    char *phone_enc = NULL;
    if (encrypt_text("系统管理员", &full_name_enc) != 0 ||
        encrypt_text("admin@local", &email_enc) != 0 ||
        encrypt_text("", &phone_enc) != 0) {
        free(full_name_enc);
        free(email_enc);
        free(phone_enc);
        fprintf(stderr, "[SECURITY] 默认管理员信息加密失败\n");
        return -1;
    }

    sqlite3_stmt *stmt = NULL;
    const char *sql =
        "INSERT INTO users (username, password_hash, role, full_name_enc, "
        "email_enc, phone_enc) VALUES (?, ?, 'admin', ?, ?, ?);";
    if (sqlite3_prepare_v2(g_db, sql, -1, &stmt, NULL) != SQLITE_OK) {
        free(full_name_enc);
        free(email_enc);
        free(phone_enc);
        fprintf(stderr, "[DB] 默认管理员插入预编译失败\n");
        return -1;
    }

    sqlite3_bind_text(stmt, 1, admin_username, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 2, password_hash, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 3, full_name_enc, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 4, email_enc, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 5, phone_enc, -1, SQLITE_TRANSIENT);

    int rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);
    free(full_name_enc);
    free(email_enc);
    free(phone_enc);

    if (rc != SQLITE_DONE) {
        fprintf(stderr, "[DB] 默认管理员创建失败\n");
        return -1;
    }

    fprintf(stdout,
            "[INFO] 已初始化默认管理员账号: %s\n"
            "[INFO] 默认管理员密码可通过环境变量 DEFAULT_ADMIN_PASSWORD 覆盖\n",
            admin_username);
    return 0;
}

static int ensure_seed_stock_movement_consistency(void) {
    sqlite3_stmt *stmt = NULL;
    int admin_user_id = 0;
    int rc = sqlite3_prepare_v2(
        g_db, "SELECT id FROM users WHERE role='admin' ORDER BY id LIMIT 1;", -1,
        &stmt, NULL);
    if (rc != SQLITE_OK) {
        fprintf(stderr, "[DB] 查询管理员失败，无法修复种子库存流水\n");
        return -1;
    }
    rc = sqlite3_step(stmt);
    if (rc == SQLITE_ROW) {
        admin_user_id = sqlite3_column_int(stmt, 0);
    }
    sqlite3_finalize(stmt);
    if (admin_user_id <= 0) {
        return 0;
    }

    int product_id = 0;
    int stock_quantity = 0;
    rc = sqlite3_prepare_v2(
        g_db, "SELECT id, stock_quantity FROM products WHERE sku=? LIMIT 1;", -1,
        &stmt, NULL);
    if (rc != SQLITE_OK) {
        fprintf(stderr, "[DB] 查询种子商品失败，无法修复种子库存流水\n");
        return -1;
    }
    sqlite3_bind_text(stmt, 1, "SEED-WATER-550", -1, SQLITE_STATIC);
    rc = sqlite3_step(stmt);
    if (rc == SQLITE_ROW) {
        product_id = sqlite3_column_int(stmt, 0);
        stock_quantity = sqlite3_column_int(stmt, 1);
    }
    sqlite3_finalize(stmt);
    if (product_id <= 0) {
        return 0;
    }

    int in_total = 0;
    int out_total = 0;
    rc = sqlite3_prepare_v2(
        g_db,
        "SELECT "
        "COALESCE(SUM(CASE WHEN movement_type='IN' THEN quantity ELSE 0 END), 0), "
        "COALESCE(SUM(CASE WHEN movement_type='OUT' THEN quantity ELSE 0 END), 0) "
        "FROM stock_movements WHERE product_id=?;",
        -1, &stmt, NULL);
    if (rc != SQLITE_OK) {
        fprintf(stderr, "[DB] 查询种子商品流水失败，无法修复种子库存流水\n");
        return -1;
    }
    sqlite3_bind_int(stmt, 1, product_id);
    rc = sqlite3_step(stmt);
    if (rc != SQLITE_ROW) {
        sqlite3_finalize(stmt);
        fprintf(stderr, "[DB] 读取种子商品流水失败，无法修复种子库存流水\n");
        return -1;
    }
    in_total = sqlite3_column_int(stmt, 0);
    out_total = sqlite3_column_int(stmt, 1);
    sqlite3_finalize(stmt);

    if (in_total > 0) {
        return 0;
    }

    int inferred_initial_in = stock_quantity + out_total;
    if (inferred_initial_in <= 0) {
        return 0;
    }

    rc = sqlite3_prepare_v2(
        g_db,
        "INSERT INTO stock_movements "
        "(product_id, movement_type, quantity, unit_price_cents, note, "
        "operator_user_id) "
        "VALUES (?, 'IN', ?, 0, '系统初始化库存补录', ?);",
        -1, &stmt, NULL);
    if (rc != SQLITE_OK) {
        fprintf(stderr, "[DB] 补录种子库存流水预编译失败\n");
        return -1;
    }
    sqlite3_bind_int(stmt, 1, product_id);
    sqlite3_bind_int(stmt, 2, inferred_initial_in);
    sqlite3_bind_int(stmt, 3, admin_user_id);
    rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);
    if (rc != SQLITE_DONE) {
        fprintf(stderr, "[DB] 补录种子库存流水失败\n");
        return -1;
    }

    fprintf(stdout, "[INFO] 已修复种子商品库存流水: sku=SEED-WATER-550, in=%d\n",
            inferred_initial_in);
    return 0;
}

static int authenticate_request(struct MHD_Connection *connection,
                                AuthUser *out_user,
                                char token_hash_hex[TOKEN_HASH_HEX_LEN + 1]) {
    const char *auth_header =
        MHD_lookup_connection_value(connection, MHD_HEADER_KIND, "Authorization");
    if (auth_header == NULL || strncmp(auth_header, "Bearer ", 7) != 0) {
        return 0;
    }

    const char *token = auth_header + 7;
    if (*token == '\0') {
        return 0;
    }

    if (hash_token(token, token_hash_hex) != 0) {
        return 0;
    }

    sqlite3_stmt *stmt = NULL;
    const char *sql =
        "SELECT u.id, u.username, u.role "
        "FROM sessions s "
        "JOIN users u ON u.id = s.user_id "
        "WHERE s.token_hash = ? AND s.expires_at > ? "
        "LIMIT 1;";

    if (sqlite3_prepare_v2(g_db, sql, -1, &stmt, NULL) != SQLITE_OK) {
        return 0;
    }

    sqlite3_bind_text(stmt, 1, token_hash_hex, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int64(stmt, 2, (sqlite3_int64)now_epoch());

    int rc = sqlite3_step(stmt);
    if (rc != SQLITE_ROW) {
        sqlite3_finalize(stmt);
        return 0;
    }

    out_user->user_id = sqlite3_column_int(stmt, 0);
    snprintf(out_user->username, sizeof(out_user->username), "%s",
             safe_col_text(stmt, 1));
    snprintf(out_user->role, sizeof(out_user->role), "%s", safe_col_text(stmt, 2));

    sqlite3_finalize(stmt);
    return 1;
}

static int is_admin_role(const AuthUser *user) {
    return strcmp(user->role, "admin") == 0;
}

static int parse_int_field(json_t *obj, const char *key, int min, int max,
                           int *out) {
    json_t *v = json_object_get(obj, key);
    if (!json_is_integer(v)) {
        return -1;
    }

    json_int_t n = json_integer_value(v);
    if (n < min || n > max) {
        return -1;
    }

    *out = (int)n;
    return 0;
}

static int require_string_field(json_t *obj, const char *key, size_t max_len,
                                const char **out) {
    json_t *v = json_object_get(obj, key);
    if (!json_is_string(v)) {
        return -1;
    }

    const char *s = json_string_value(v);
    if (s == NULL) {
        return -1;
    }

    size_t len = strlen(s);
    if (len == 0 || len > max_len) {
        return -1;
    }

    *out = s;
    return 0;
}

static const char *optional_string_field(json_t *obj, const char *key,
                                         size_t max_len) {
    json_t *v = json_object_get(obj, key);
    if (v == NULL || json_is_null(v)) {
        return "";
    }
    if (!json_is_string(v)) {
        return NULL;
    }

    const char *s = json_string_value(v);
    if (s == NULL || strlen(s) > max_len) {
        return NULL;
    }
    return s;
}

static enum MHD_Result handle_health(struct MHD_Connection *connection) {
    json_t *data = json_object();
    json_object_set_new(data, "service", json_string("jinxiaocun-backend-c"));
    json_object_set_new(data, "status", json_string("ok"));
    json_object_set_new(data, "timestamp", json_integer((json_int_t)now_epoch()));
    return respond_success(connection, MHD_HTTP_OK, data);
}

static enum MHD_Result handle_register(struct MHD_Connection *connection,
                                       ConnectionInfo *ci) {
    char err[256];
    json_t *body = NULL;
    if (parse_json_body(ci, &body, err) != 0) {
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_JSON", err);
    }

    const char *username = NULL;
    const char *password = NULL;
    if (require_string_field(body, "username", 64, &username) != 0 ||
        require_string_field(body, "password", 128, &password) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "username/password 必填，且长度必须合法");
    }

    const char *full_name = optional_string_field(body, "full_name", 128);
    const char *email = optional_string_field(body, "email", 128);
    const char *phone = optional_string_field(body, "phone", 64);
    if (full_name == NULL || email == NULL || phone == NULL) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "full_name/email/phone 必须是字符串且长度合法");
    }

    const char *role_input = optional_string_field(body, "role", 16);
    if (role_input == NULL) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "role 必须是字符串");
    }

    pthread_mutex_lock(&g_db_mutex);

    int user_count = 0;
    if (db_user_count(&user_count) != 0) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询用户数量失败");
    }

    AuthUser creator;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    const int first_user = (user_count == 0);
    if (!first_user) {
        if (!authenticate_request(connection, &creator, token_hash)) {
            pthread_mutex_unlock(&g_db_mutex);
            json_decref(body);
            return respond_error(connection, MHD_HTTP_UNAUTHORIZED,
                                "UNAUTHORIZED", "需要管理员身份创建用户");
        }
        if (!is_admin_role(&creator)) {
            pthread_mutex_unlock(&g_db_mutex);
            json_decref(body);
            return respond_error(connection, MHD_HTTP_FORBIDDEN, "FORBIDDEN",
                                "仅管理员可创建用户");
        }
    }

    const char *role = "staff";
    if (first_user) {
        role = "admin";
    } else if (role_input != NULL && *role_input != '\0') {
        if (strcmp(role_input, "admin") != 0 && strcmp(role_input, "staff") != 0) {
            pthread_mutex_unlock(&g_db_mutex);
            json_decref(body);
            return respond_error(connection, MHD_HTTP_BAD_REQUEST,
                                "INVALID_INPUT", "role 仅支持 admin/staff");
        }
        role = role_input;
    }

    char username_copy[65];
    char role_copy[17];
    snprintf(username_copy, sizeof(username_copy), "%s", username);
    snprintf(role_copy, sizeof(role_copy), "%s", role);

    char password_hash[crypto_pwhash_STRBYTES];
    if (crypto_pwhash_str(password_hash, password, strlen(password),
                          crypto_pwhash_OPSLIMIT_INTERACTIVE,
                          crypto_pwhash_MEMLIMIT_INTERACTIVE) != 0) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "SECURITY_ERROR", "密码加密失败");
    }

    char *full_name_enc = NULL;
    char *email_enc = NULL;
    char *phone_enc = NULL;
    if (encrypt_text(full_name, &full_name_enc) != 0 ||
        encrypt_text(email, &email_enc) != 0 ||
        encrypt_text(phone, &phone_enc) != 0) {
        free(full_name_enc);
        free(email_enc);
        free(phone_enc);
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "SECURITY_ERROR", "用户信息加密失败");
    }

    sqlite3_stmt *stmt = NULL;
    const char *sql =
        "INSERT INTO users (username, password_hash, role, full_name_enc, "
        "email_enc, phone_enc) VALUES (?, ?, ?, ?, ?, ?);";

    if (sqlite3_prepare_v2(g_db, sql, -1, &stmt, NULL) != SQLITE_OK) {
        free(full_name_enc);
        free(email_enc);
        free(phone_enc);
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "创建用户预编译失败");
    }

    sqlite3_bind_text(stmt, 1, username_copy, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 2, password_hash, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 3, role_copy, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 4, full_name_enc, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 5, email_enc, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 6, phone_enc, -1, SQLITE_TRANSIENT);

    int rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);
    free(full_name_enc);
    free(email_enc);
    free(phone_enc);
    pthread_mutex_unlock(&g_db_mutex);
    json_decref(body);

    if (rc != SQLITE_DONE) {
        if (rc == SQLITE_CONSTRAINT) {
            return respond_error(connection, MHD_HTTP_CONFLICT, "CONFLICT",
                                "用户名已存在");
        }
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "创建用户失败");
    }

    json_t *data = json_object();
    json_object_set_new(data, "username", json_string(username_copy));
    json_object_set_new(data, "role", json_string(role_copy));
    json_object_set_new(data, "first_user", first_user ? json_true() : json_false());
    return respond_success(connection, MHD_HTTP_CREATED, data);
}

static enum MHD_Result handle_login(struct MHD_Connection *connection,
                                    ConnectionInfo *ci) {
    char err[256];
    json_t *body = NULL;
    if (parse_json_body(ci, &body, err) != 0) {
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_JSON", err);
    }

    const char *username = NULL;
    const char *password = NULL;
    if (require_string_field(body, "username", 64, &username) != 0 ||
        require_string_field(body, "password", 128, &password) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "username/password 必填");
    }

    char username_copy[65];
    snprintf(username_copy, sizeof(username_copy), "%s", username);

    pthread_mutex_lock(&g_db_mutex);

    sqlite3_stmt *stmt = NULL;
    const char *sql =
        "SELECT id, password_hash, role FROM users WHERE username = ? LIMIT 1;";
    if (sqlite3_prepare_v2(g_db, sql, -1, &stmt, NULL) != SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "数据库查询失败");
    }

    sqlite3_bind_text(stmt, 1, username, -1, SQLITE_TRANSIENT);
    int rc = sqlite3_step(stmt);
    if (rc != SQLITE_ROW) {
        sqlite3_finalize(stmt);
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_UNAUTHORIZED, "UNAUTHORIZED",
                            "用户名或密码错误");
    }

    int user_id = sqlite3_column_int(stmt, 0);
    const char *password_hash = safe_col_text(stmt, 1);
    char role_copy[32];
    snprintf(role_copy, sizeof(role_copy), "%s", safe_col_text(stmt, 2));

    if (crypto_pwhash_str_verify(password_hash, password, strlen(password)) != 0) {
        sqlite3_finalize(stmt);
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_UNAUTHORIZED, "UNAUTHORIZED",
                            "用户名或密码错误");
    }
    sqlite3_finalize(stmt);

    char token[128] = {0};
    if (generate_access_token(token, sizeof(token)) != 0) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "SECURITY_ERROR", "生成令牌失败");
    }

    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    if (hash_token(token, token_hash) != 0) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "SECURITY_ERROR", "处理令牌失败");
    }

    const time_t expires_at = now_epoch() + (time_t)g_cfg.session_ttl_hours * 3600;

    if (db_exec("DELETE FROM sessions WHERE expires_at <= strftime('%s', 'now');") != 0) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "会话清理失败");
    }

    const char *insert_sql =
        "INSERT INTO sessions (user_id, token_hash, expires_at) VALUES (?, ?, ?);";
    if (sqlite3_prepare_v2(g_db, insert_sql, -1, &stmt, NULL) != SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "会话创建失败");
    }

    sqlite3_bind_int(stmt, 1, user_id);
    sqlite3_bind_text(stmt, 2, token_hash, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int64(stmt, 3, (sqlite3_int64)expires_at);

    rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);
    pthread_mutex_unlock(&g_db_mutex);
    json_decref(body);

    if (rc != SQLITE_DONE) {
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "会话创建失败");
    }

    json_t *data = json_object();
    json_object_set_new(data, "access_token", json_string(token));
    json_object_set_new(data, "token_type", json_string("Bearer"));
    json_object_set_new(data, "expires_at", json_integer((json_int_t)expires_at));
    json_object_set_new(data, "user_id", json_integer(user_id));
    json_object_set_new(data, "username", json_string(username_copy));
    json_object_set_new(data, "role", json_string(role_copy));
    return respond_success(connection, MHD_HTTP_OK, data);
}

static enum MHD_Result handle_logout(struct MHD_Connection *connection) {
    pthread_mutex_lock(&g_db_mutex);

    AuthUser user;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    if (!authenticate_request(connection, &user, token_hash)) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_UNAUTHORIZED, "UNAUTHORIZED",
                            "未登录或令牌无效");
    }

    sqlite3_stmt *stmt = NULL;
    if (sqlite3_prepare_v2(g_db, "DELETE FROM sessions WHERE token_hash = ?;", -1,
                           &stmt, NULL) != SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "退出登录失败");
    }

    sqlite3_bind_text(stmt, 1, token_hash, -1, SQLITE_TRANSIENT);
    sqlite3_step(stmt);
    sqlite3_finalize(stmt);

    pthread_mutex_unlock(&g_db_mutex);

    json_t *data = json_object();
    json_object_set_new(data, "message", json_string("已退出登录"));
    return respond_success(connection, MHD_HTTP_OK, data);
}

static enum MHD_Result handle_auth_me(struct MHD_Connection *connection) {
    pthread_mutex_lock(&g_db_mutex);

    AuthUser user;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    if (!authenticate_request(connection, &user, token_hash)) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_UNAUTHORIZED, "UNAUTHORIZED",
                            "未登录或令牌无效");
    }

    sqlite3_stmt *stmt = NULL;
    const char *sql =
        "SELECT full_name_enc, email_enc, phone_enc, created_at "
        "FROM users WHERE id = ? LIMIT 1;";

    if (sqlite3_prepare_v2(g_db, sql, -1, &stmt, NULL) != SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询用户详情失败");
    }

    sqlite3_bind_int(stmt, 1, user.user_id);
    int rc = sqlite3_step(stmt);
    if (rc != SQLITE_ROW) {
        sqlite3_finalize(stmt);
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_NOT_FOUND, "NOT_FOUND",
                            "用户不存在");
    }

    const char *full_name_enc = safe_col_text(stmt, 0);
    const char *email_enc = safe_col_text(stmt, 1);
    const char *phone_enc = safe_col_text(stmt, 2);
    char created_at[64];
    snprintf(created_at, sizeof(created_at), "%s", safe_col_text(stmt, 3));

    char *full_name = NULL;
    char *email = NULL;
    char *phone = NULL;

    int ok = decrypt_text(full_name_enc, &full_name) == 0 &&
             decrypt_text(email_enc, &email) == 0 &&
             decrypt_text(phone_enc, &phone) == 0;

    sqlite3_finalize(stmt);
    pthread_mutex_unlock(&g_db_mutex);

    if (!ok) {
        free(full_name);
        free(email);
        free(phone);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "SECURITY_ERROR", "解密用户信息失败");
    }

    json_t *data = json_object();
    json_object_set_new(data, "user_id", json_integer(user.user_id));
    json_object_set_new(data, "username", json_string(user.username));
    json_object_set_new(data, "role", json_string(user.role));
    json_object_set_new(data, "full_name", json_string(full_name));
    json_object_set_new(data, "email", json_string(email));
    json_object_set_new(data, "phone", json_string(phone));
    json_object_set_new(data, "created_at", json_string(created_at));

    free(full_name);
    free(email);
    free(phone);

    return respond_success(connection, MHD_HTTP_OK, data);
}

static enum MHD_Result handle_create_product(struct MHD_Connection *connection,
                                             ConnectionInfo *ci) {
    char err[256];
    json_t *body = NULL;
    if (parse_json_body(ci, &body, err) != 0) {
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_JSON", err);
    }

    const char *sku = NULL;
    const char *name = NULL;
    if (require_string_field(body, "sku", 64, &sku) != 0 ||
        require_string_field(body, "name", 128, &name) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "sku/name 必填");
    }

    const char *unit = optional_string_field(body, "unit", 16);
    if (unit == NULL || *unit == '\0') {
        unit = "瓶";
    }

    char sku_copy[65];
    char name_copy[129];
    char unit_copy[17];
    snprintf(sku_copy, sizeof(sku_copy), "%s", sku);
    snprintf(name_copy, sizeof(name_copy), "%s", name);
    snprintf(unit_copy, sizeof(unit_copy), "%s", unit);

    pthread_mutex_lock(&g_db_mutex);

    AuthUser user;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    if (!authenticate_request(connection, &user, token_hash)) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_UNAUTHORIZED, "UNAUTHORIZED",
                            "需要登录");
    }

    if (!is_admin_role(&user)) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_FORBIDDEN, "FORBIDDEN",
                            "仅管理员可新增商品");
    }

    sqlite3_stmt *stmt = NULL;
    const char *sql =
        "INSERT INTO products (sku, name, unit, stock_quantity) VALUES (?, ?, ?, 0);";

    if (sqlite3_prepare_v2(g_db, sql, -1, &stmt, NULL) != SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "新增商品失败");
    }

    sqlite3_bind_text(stmt, 1, sku_copy, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 2, name_copy, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 3, unit_copy, -1, SQLITE_TRANSIENT);

    int rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);
    pthread_mutex_unlock(&g_db_mutex);
    json_decref(body);

    if (rc != SQLITE_DONE) {
        if (rc == SQLITE_CONSTRAINT) {
            return respond_error(connection, MHD_HTTP_CONFLICT, "CONFLICT",
                                "商品 SKU 已存在");
        }
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "新增商品失败");
    }

    json_t *data = json_object();
    json_object_set_new(data, "sku", json_string(sku_copy));
    json_object_set_new(data, "name", json_string(name_copy));
    json_object_set_new(data, "unit", json_string(unit_copy));
    return respond_success(connection, MHD_HTTP_CREATED, data);
}

static enum MHD_Result handle_list_products(struct MHD_Connection *connection) {
    pthread_mutex_lock(&g_db_mutex);

    sqlite3_stmt *stmt = NULL;
    const char *sql =
        "SELECT id, sku, name, unit, stock_quantity, created_at, updated_at "
        "FROM products ORDER BY id DESC;";

    if (sqlite3_prepare_v2(g_db, sql, -1, &stmt, NULL) != SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询商品列表失败");
    }

    json_t *items = json_array();
    int rc = SQLITE_OK;
    while ((rc = sqlite3_step(stmt)) == SQLITE_ROW) {
        json_t *item = json_object();
        json_object_set_new(item, "id", json_integer(sqlite3_column_int(stmt, 0)));
        json_object_set_new(item, "sku", json_string(safe_col_text(stmt, 1)));
        json_object_set_new(item, "name", json_string(safe_col_text(stmt, 2)));
        json_object_set_new(item, "unit", json_string(safe_col_text(stmt, 3)));
        json_object_set_new(item, "stock_quantity",
                            json_integer(sqlite3_column_int(stmt, 4)));
        json_object_set_new(item, "created_at", json_string(safe_col_text(stmt, 5)));
        json_object_set_new(item, "updated_at", json_string(safe_col_text(stmt, 6)));
        json_array_append_new(items, item);
    }

    sqlite3_finalize(stmt);
    pthread_mutex_unlock(&g_db_mutex);

    if (rc != SQLITE_DONE) {
        json_decref(items);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "读取商品列表失败");
    }

    return respond_success(connection, MHD_HTTP_OK, items);
}

static int begin_transaction(void) {
    return db_exec("BEGIN IMMEDIATE TRANSACTION;");
}

static void rollback_transaction(void) { db_exec("ROLLBACK;"); }

static int commit_transaction(void) { return db_exec("COMMIT;"); }

static enum MHD_Result handle_inbound(struct MHD_Connection *connection,
                                      ConnectionInfo *ci) {
    char err[256];
    json_t *body = NULL;
    if (parse_json_body(ci, &body, err) != 0) {
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_JSON", err);
    }

    const char *sku = NULL;
    if (require_string_field(body, "sku", 64, &sku) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "sku 必填");
    }

    int quantity = 0;
    int unit_cost = 0;
    if (parse_int_field(body, "quantity", 1, 1000000, &quantity) != 0 ||
        parse_int_field(body, "unit_cost_cents", 0, 100000000, &unit_cost) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "quantity/unit_cost_cents 必须为合法整数");
    }

    const char *note = optional_string_field(body, "note", 256);
    if (note == NULL) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "note 需为字符串且不超过256字符");
    }

    char sku_copy[65];
    snprintf(sku_copy, sizeof(sku_copy), "%s", sku);

    pthread_mutex_lock(&g_db_mutex);

    AuthUser user;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    if (!authenticate_request(connection, &user, token_hash)) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_UNAUTHORIZED, "UNAUTHORIZED",
                            "需要登录");
    }

    if (begin_transaction() != 0) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "开启事务失败");
    }

    sqlite3_stmt *stmt = NULL;
    int product_id = 0;
    int current_stock = 0;

    const char *find_sql =
        "SELECT id, stock_quantity FROM products WHERE sku = ? LIMIT 1;";
    if (sqlite3_prepare_v2(g_db, find_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询商品失败");
    }

    sqlite3_bind_text(stmt, 1, sku_copy, -1, SQLITE_TRANSIENT);
    int rc = sqlite3_step(stmt);
    if (rc != SQLITE_ROW) {
        sqlite3_finalize(stmt);
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_NOT_FOUND, "NOT_FOUND",
                            "商品不存在");
    }

    product_id = sqlite3_column_int(stmt, 0);
    current_stock = sqlite3_column_int(stmt, 1);
    sqlite3_finalize(stmt);

    const int new_stock = current_stock + quantity;

    const char *update_sql =
        "UPDATE products SET stock_quantity = ?, updated_at = CURRENT_TIMESTAMP "
        "WHERE id = ?;";
    if (sqlite3_prepare_v2(g_db, update_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "更新库存失败");
    }

    sqlite3_bind_int(stmt, 1, new_stock);
    sqlite3_bind_int(stmt, 2, product_id);
    rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);
    if (rc != SQLITE_DONE) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "更新库存失败");
    }

    const char *ins_sql =
        "INSERT INTO stock_movements "
        "(product_id, movement_type, quantity, unit_price_cents, note, "
        "operator_user_id) "
        "VALUES (?, 'IN', ?, ?, ?, ?);";

    if (sqlite3_prepare_v2(g_db, ins_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "写入流水失败");
    }

    sqlite3_bind_int(stmt, 1, product_id);
    sqlite3_bind_int(stmt, 2, quantity);
    sqlite3_bind_int(stmt, 3, unit_cost);
    sqlite3_bind_text(stmt, 4, note, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int(stmt, 5, user.user_id);
    rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);

    if (rc != SQLITE_DONE || commit_transaction() != 0) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "提交入库事务失败");
    }

    pthread_mutex_unlock(&g_db_mutex);
    json_decref(body);

    json_t *data = json_object();
    json_object_set_new(data, "sku", json_string(sku_copy));
    json_object_set_new(data, "movement_type", json_string("IN"));
    json_object_set_new(data, "quantity", json_integer(quantity));
    json_object_set_new(data, "new_stock", json_integer(new_stock));
    json_object_set_new(data, "operator", json_string(user.username));
    return respond_success(connection, MHD_HTTP_OK, data);
}

static enum MHD_Result handle_sales(struct MHD_Connection *connection,
                                    ConnectionInfo *ci) {
    char err[256];
    json_t *body = NULL;
    if (parse_json_body(ci, &body, err) != 0) {
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_JSON", err);
    }

    const char *sku = NULL;
    if (require_string_field(body, "sku", 64, &sku) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "sku 必填");
    }

    int quantity = 0;
    int sale_price = 0;
    if (parse_int_field(body, "quantity", 1, 1000000, &quantity) != 0 ||
        parse_int_field(body, "unit_price_cents", 0, 100000000, &sale_price) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "quantity/unit_price_cents 必须为合法整数");
    }

    const char *note = optional_string_field(body, "note", 256);
    if (note == NULL) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "note 需为字符串且不超过256字符");
    }

    char sku_copy[65];
    snprintf(sku_copy, sizeof(sku_copy), "%s", sku);

    pthread_mutex_lock(&g_db_mutex);

    AuthUser user;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    if (!authenticate_request(connection, &user, token_hash)) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_UNAUTHORIZED, "UNAUTHORIZED",
                            "需要登录");
    }

    if (begin_transaction() != 0) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "开启事务失败");
    }

    sqlite3_stmt *stmt = NULL;
    int product_id = 0;
    int current_stock = 0;

    const char *find_sql =
        "SELECT id, stock_quantity FROM products WHERE sku = ? LIMIT 1;";
    if (sqlite3_prepare_v2(g_db, find_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询商品失败");
    }

    sqlite3_bind_text(stmt, 1, sku_copy, -1, SQLITE_TRANSIENT);
    int rc = sqlite3_step(stmt);
    if (rc != SQLITE_ROW) {
        sqlite3_finalize(stmt);
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_NOT_FOUND, "NOT_FOUND",
                            "商品不存在");
    }

    product_id = sqlite3_column_int(stmt, 0);
    current_stock = sqlite3_column_int(stmt, 1);
    sqlite3_finalize(stmt);

    if (current_stock < quantity) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_CONFLICT, "INSUFFICIENT_STOCK",
                            "库存不足，无法出库");
    }

    const int new_stock = current_stock - quantity;

    const char *update_sql =
        "UPDATE products SET stock_quantity = ?, updated_at = CURRENT_TIMESTAMP "
        "WHERE id = ?;";
    if (sqlite3_prepare_v2(g_db, update_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "更新库存失败");
    }

    sqlite3_bind_int(stmt, 1, new_stock);
    sqlite3_bind_int(stmt, 2, product_id);
    rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);
    if (rc != SQLITE_DONE) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "更新库存失败");
    }

    const char *ins_sql =
        "INSERT INTO stock_movements "
        "(product_id, movement_type, quantity, unit_price_cents, note, "
        "operator_user_id) "
        "VALUES (?, 'OUT', ?, ?, ?, ?);";

    if (sqlite3_prepare_v2(g_db, ins_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "写入流水失败");
    }

    sqlite3_bind_int(stmt, 1, product_id);
    sqlite3_bind_int(stmt, 2, quantity);
    sqlite3_bind_int(stmt, 3, sale_price);
    sqlite3_bind_text(stmt, 4, note, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int(stmt, 5, user.user_id);

    rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);

    if (rc != SQLITE_DONE || commit_transaction() != 0) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "提交出库事务失败");
    }

    pthread_mutex_unlock(&g_db_mutex);
    json_decref(body);

    json_t *data = json_object();
    json_object_set_new(data, "sku", json_string(sku_copy));
    json_object_set_new(data, "movement_type", json_string("OUT"));
    json_object_set_new(data, "quantity", json_integer(quantity));
    json_object_set_new(data, "new_stock", json_integer(new_stock));
    json_object_set_new(data, "operator", json_string(user.username));
    return respond_success(connection, MHD_HTTP_OK, data);
}

static enum MHD_Result handle_inventory(struct MHD_Connection *connection) {
    pthread_mutex_lock(&g_db_mutex);

    sqlite3_stmt *summary_stmt = NULL;
    const char *summary_sql =
        "SELECT "
        "  (SELECT COUNT(*) FROM products),"
        "  (SELECT COALESCE(SUM(stock_quantity), 0) FROM products),"
        "  (SELECT COALESCE(SUM(quantity), 0) FROM stock_movements WHERE "
        "movement_type='IN'),"
        "  (SELECT COALESCE(SUM(quantity), 0) FROM stock_movements WHERE "
        "movement_type='OUT');";

    if (sqlite3_prepare_v2(g_db, summary_sql, -1, &summary_stmt, NULL) !=
        SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询库存汇总失败");
    }

    int rc = sqlite3_step(summary_stmt);
    if (rc != SQLITE_ROW) {
        sqlite3_finalize(summary_stmt);
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询库存汇总失败");
    }

    int product_count = sqlite3_column_int(summary_stmt, 0);
    int total_stock = sqlite3_column_int(summary_stmt, 1);
    int total_in = sqlite3_column_int(summary_stmt, 2);
    int total_out = sqlite3_column_int(summary_stmt, 3);
    sqlite3_finalize(summary_stmt);

    sqlite3_stmt *list_stmt = NULL;
    const char *list_sql =
        "SELECT sku, name, unit, stock_quantity, updated_at "
        "FROM products ORDER BY stock_quantity DESC, id ASC;";
    if (sqlite3_prepare_v2(g_db, list_sql, -1, &list_stmt, NULL) != SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询库存明细失败");
    }

    json_t *products = json_array();
    while ((rc = sqlite3_step(list_stmt)) == SQLITE_ROW) {
        json_t *item = json_object();
        json_object_set_new(item, "sku", json_string(safe_col_text(list_stmt, 0)));
        json_object_set_new(item, "name", json_string(safe_col_text(list_stmt, 1)));
        json_object_set_new(item, "unit", json_string(safe_col_text(list_stmt, 2)));
        json_object_set_new(item, "stock_quantity",
                            json_integer(sqlite3_column_int(list_stmt, 3)));
        json_object_set_new(item, "updated_at",
                            json_string(safe_col_text(list_stmt, 4)));
        json_array_append_new(products, item);
    }

    sqlite3_finalize(list_stmt);
    pthread_mutex_unlock(&g_db_mutex);

    if (rc != SQLITE_DONE) {
        json_decref(products);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "读取库存明细失败");
    }

    json_t *data = json_object();
    json_t *summary = json_object();
    json_object_set_new(summary, "product_count", json_integer(product_count));
    json_object_set_new(summary, "total_stock_quantity", json_integer(total_stock));
    json_object_set_new(summary, "total_in_quantity", json_integer(total_in));
    json_object_set_new(summary, "total_out_quantity", json_integer(total_out));

    json_object_set_new(data, "summary", summary);
    json_object_set_new(data, "products", products);

    return respond_success(connection, MHD_HTTP_OK, data);
}

static int parse_limit_query(struct MHD_Connection *connection) {
    const char *limit_s =
        MHD_lookup_connection_value(connection, MHD_GET_ARGUMENT_KIND, "limit");
    if (limit_s == NULL || *limit_s == '\0') {
        return 50;
    }

    char *end = NULL;
    errno = 0;
    long v = strtol(limit_s, &end, 10);
    if (errno != 0 || end == limit_s || *end != '\0') {
        return 50;
    }
    if (v < 1) {
        v = 1;
    }
    if (v > 200) {
        v = 200;
    }
    return (int)v;
}

static enum MHD_Result handle_movements(struct MHD_Connection *connection) {
    pthread_mutex_lock(&g_db_mutex);

    AuthUser user;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    if (!authenticate_request(connection, &user, token_hash)) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_UNAUTHORIZED, "UNAUTHORIZED",
                            "需要登录");
    }

    const char *type =
        MHD_lookup_connection_value(connection, MHD_GET_ARGUMENT_KIND, "type");
    int use_type = 0;
    if (type != NULL && *type != '\0') {
        if (strcmp(type, "IN") == 0 || strcmp(type, "OUT") == 0) {
            use_type = 1;
        } else {
            pthread_mutex_unlock(&g_db_mutex);
            return respond_error(connection, MHD_HTTP_BAD_REQUEST,
                                "INVALID_INPUT", "type 仅支持 IN 或 OUT");
        }
    }

    int limit = parse_limit_query(connection);

    sqlite3_stmt *stmt = NULL;
    const char *sql_all =
        "SELECT m.id, p.sku, p.name, m.movement_type, m.quantity, "
        "m.unit_price_cents, m.note, u.username, m.created_at "
        "FROM stock_movements m "
        "JOIN products p ON p.id = m.product_id "
        "JOIN users u ON u.id = m.operator_user_id "
        "ORDER BY m.id DESC LIMIT ?;";

    const char *sql_type =
        "SELECT m.id, p.sku, p.name, m.movement_type, m.quantity, "
        "m.unit_price_cents, m.note, u.username, m.created_at "
        "FROM stock_movements m "
        "JOIN products p ON p.id = m.product_id "
        "JOIN users u ON u.id = m.operator_user_id "
        "WHERE m.movement_type = ? "
        "ORDER BY m.id DESC LIMIT ?;";

    if (sqlite3_prepare_v2(g_db, use_type ? sql_type : sql_all, -1, &stmt, NULL) !=
        SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询流水失败");
    }

    int idx = 1;
    if (use_type) {
        sqlite3_bind_text(stmt, idx++, type, -1, SQLITE_TRANSIENT);
    }
    sqlite3_bind_int(stmt, idx, limit);

    json_t *items = json_array();
    int rc = SQLITE_OK;
    while ((rc = sqlite3_step(stmt)) == SQLITE_ROW) {
        json_t *it = json_object();
        json_object_set_new(it, "id", json_integer(sqlite3_column_int(stmt, 0)));
        json_object_set_new(it, "sku", json_string(safe_col_text(stmt, 1)));
        json_object_set_new(it, "product_name", json_string(safe_col_text(stmt, 2)));
        json_object_set_new(it, "movement_type", json_string(safe_col_text(stmt, 3)));
        json_object_set_new(it, "quantity", json_integer(sqlite3_column_int(stmt, 4)));
        json_object_set_new(it, "unit_price_cents",
                            json_integer(sqlite3_column_int(stmt, 5)));
        json_object_set_new(it, "note", json_string(safe_col_text(stmt, 6)));
        json_object_set_new(it, "operator", json_string(safe_col_text(stmt, 7)));
        json_object_set_new(it, "created_at", json_string(safe_col_text(stmt, 8)));
        json_array_append_new(items, it);
    }

    sqlite3_finalize(stmt);
    pthread_mutex_unlock(&g_db_mutex);

    if (rc != SQLITE_DONE) {
        json_decref(items);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "读取流水失败");
    }

    return respond_success(connection, MHD_HTTP_OK, items);
}

static enum MHD_Result handle_create_supplier(struct MHD_Connection *connection,
                                              ConnectionInfo *ci) {
    char err[256];
    json_t *body = NULL;
    if (parse_json_body(ci, &body, err) != 0) {
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_JSON", err);
    }

    const char *name = NULL;
    if (require_string_field(body, "name", 128, &name) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "name 必填");
    }

    const char *contact_name = optional_string_field(body, "contact_name", 64);
    const char *contact_phone = optional_string_field(body, "contact_phone", 32);
    if (contact_name == NULL || contact_phone == NULL) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "contact_name/contact_phone 必须是字符串");
    }

    char name_copy[129];
    char contact_name_copy[65];
    char contact_phone_copy[33];
    snprintf(name_copy, sizeof(name_copy), "%s", name);
    snprintf(contact_name_copy, sizeof(contact_name_copy), "%s",
             contact_name ? contact_name : "");
    snprintf(contact_phone_copy, sizeof(contact_phone_copy), "%s",
             contact_phone ? contact_phone : "");

    pthread_mutex_lock(&g_db_mutex);

    AuthUser user;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    if (!authenticate_request(connection, &user, token_hash)) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_UNAUTHORIZED, "UNAUTHORIZED",
                            "需要登录");
    }

    if (!is_admin_role(&user)) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_FORBIDDEN, "FORBIDDEN",
                            "仅管理员可新增供应商");
    }

    sqlite3_stmt *stmt = NULL;
    const char *sql =
        "INSERT INTO suppliers (name, contact_name, contact_phone) VALUES (?, ?, ?);";

    if (sqlite3_prepare_v2(g_db, sql, -1, &stmt, NULL) != SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "新增供应商失败");
    }

    sqlite3_bind_text(stmt, 1, name_copy, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 2, contact_name_copy, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 3, contact_phone_copy, -1, SQLITE_TRANSIENT);

    int rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);
    pthread_mutex_unlock(&g_db_mutex);
    json_decref(body);

    if (rc != SQLITE_DONE) {
        if (rc == SQLITE_CONSTRAINT) {
            return respond_error(connection, MHD_HTTP_CONFLICT, "CONFLICT",
                                "供应商名称已存在");
        }
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "新增供应商失败");
    }

    json_t *data = json_object();
    json_object_set_new(data, "name", json_string(name_copy));
    return respond_success(connection, MHD_HTTP_CREATED, data);
}

static enum MHD_Result handle_list_suppliers(struct MHD_Connection *connection) {
    pthread_mutex_lock(&g_db_mutex);

    AuthUser user;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    if (!authenticate_request(connection, &user, token_hash)) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_UNAUTHORIZED, "UNAUTHORIZED",
                            "需要登录");
    }

    sqlite3_stmt *stmt = NULL;
    const char *sql =
        "SELECT id, name, contact_name, contact_phone, created_at "
        "FROM suppliers ORDER BY id DESC;";

    if (sqlite3_prepare_v2(g_db, sql, -1, &stmt, NULL) != SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询供应商列表失败");
    }

    json_t *items = json_array();
    int rc = SQLITE_OK;
    while ((rc = sqlite3_step(stmt)) == SQLITE_ROW) {
        json_t *it = json_object();
        json_object_set_new(it, "id", json_integer(sqlite3_column_int(stmt, 0)));
        json_object_set_new(it, "name", json_string(safe_col_text(stmt, 1)));
        json_object_set_new(it, "contact_name",
                            json_string(safe_col_text(stmt, 2)));
        json_object_set_new(it, "contact_phone",
                            json_string(safe_col_text(stmt, 3)));
        json_object_set_new(it, "created_at",
                            json_string(safe_col_text(stmt, 4)));
        json_array_append_new(items, it);
    }

    sqlite3_finalize(stmt);
    pthread_mutex_unlock(&g_db_mutex);

    if (rc != SQLITE_DONE) {
        json_decref(items);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "读取供应商列表失败");
    }

    return respond_success(connection, MHD_HTTP_OK, items);
}

static enum MHD_Result handle_create_cabinet(struct MHD_Connection *connection,
                                             ConnectionInfo *ci) {
    char err[256];
    json_t *body = NULL;
    if (parse_json_body(ci, &body, err) != 0) {
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_JSON", err);
    }

    const char *cabinet_code = NULL;
    const char *name = NULL;
    if (require_string_field(body, "cabinet_code", 32, &cabinet_code) != 0 ||
        require_string_field(body, "name", 128, &name) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "cabinet_code/name 必填");
    }

    const char *location = optional_string_field(body, "location", 256);
    const char *status = optional_string_field(body, "status", 16);
    if (location == NULL || status == NULL) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "location/status 必须是字符串");
    }

    char cabinet_code_copy[33];
    char name_copy[129];
    char location_copy[257];
    char status_copy[17];
    snprintf(cabinet_code_copy, sizeof(cabinet_code_copy), "%s", cabinet_code);
    snprintf(name_copy, sizeof(name_copy), "%s", name);
    snprintf(location_copy, sizeof(location_copy), "%s",
             location ? location : "");
    snprintf(status_copy, sizeof(status_copy), "%s",
             (status && *status) ? status : "active");

    if (strcmp(status_copy, "active") != 0 &&
        strcmp(status_copy, "inactive") != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "status 仅支持 active/inactive");
    }

    pthread_mutex_lock(&g_db_mutex);

    AuthUser user;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    if (!authenticate_request(connection, &user, token_hash)) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_UNAUTHORIZED, "UNAUTHORIZED",
                            "需要登录");
    }

    if (!is_admin_role(&user)) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_FORBIDDEN, "FORBIDDEN",
                            "仅管理员可新增柜机");
    }

    sqlite3_stmt *stmt = NULL;
    const char *sql =
        "INSERT INTO cabinets (cabinet_code, name, location, status) VALUES (?, ?, ?, ?);";

    if (sqlite3_prepare_v2(g_db, sql, -1, &stmt, NULL) != SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "新增柜机失败");
    }

    sqlite3_bind_text(stmt, 1, cabinet_code_copy, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 2, name_copy, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 3, location_copy, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 4, status_copy, -1, SQLITE_TRANSIENT);

    int rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);
    pthread_mutex_unlock(&g_db_mutex);
    json_decref(body);

    if (rc != SQLITE_DONE) {
        if (rc == SQLITE_CONSTRAINT) {
            return respond_error(connection, MHD_HTTP_CONFLICT, "CONFLICT",
                                "柜机编号已存在");
        }
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "新增柜机失败");
    }

    json_t *data = json_object();
    json_object_set_new(data, "cabinet_code", json_string(cabinet_code_copy));
    json_object_set_new(data, "name", json_string(name_copy));
    return respond_success(connection, MHD_HTTP_CREATED, data);
}

static enum MHD_Result handle_list_cabinets(struct MHD_Connection *connection) {
    pthread_mutex_lock(&g_db_mutex);

    AuthUser user;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    if (!authenticate_request(connection, &user, token_hash)) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_UNAUTHORIZED, "UNAUTHORIZED",
                            "需要登录");
    }

    sqlite3_stmt *stmt = NULL;
    const char *sql =
        "SELECT id, cabinet_code, name, location, status, created_at "
        "FROM cabinets ORDER BY id DESC;";

    if (sqlite3_prepare_v2(g_db, sql, -1, &stmt, NULL) != SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询柜机列表失败");
    }

    json_t *items = json_array();
    int rc = SQLITE_OK;
    while ((rc = sqlite3_step(stmt)) == SQLITE_ROW) {
        json_t *it = json_object();
        json_object_set_new(it, "id", json_integer(sqlite3_column_int(stmt, 0)));
        json_object_set_new(it, "cabinet_code",
                            json_string(safe_col_text(stmt, 1)));
        json_object_set_new(it, "name", json_string(safe_col_text(stmt, 2)));
        json_object_set_new(it, "location",
                            json_string(safe_col_text(stmt, 3)));
        json_object_set_new(it, "status", json_string(safe_col_text(stmt, 4)));
        json_object_set_new(it, "created_at",
                            json_string(safe_col_text(stmt, 5)));
        json_array_append_new(items, it);
    }

    sqlite3_finalize(stmt);
    pthread_mutex_unlock(&g_db_mutex);

    if (rc != SQLITE_DONE) {
        json_decref(items);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "读取柜机列表失败");
    }

    return respond_success(connection, MHD_HTTP_OK, items);
}

static enum MHD_Result handle_create_batch(struct MHD_Connection *connection,
                                           ConnectionInfo *ci) {
    char err[256];
    json_t *body = NULL;
    if (parse_json_body(ci, &body, err) != 0) {
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_JSON", err);
    }

    const char *sku = NULL;
    const char *batch_no = NULL;
    const char *supplier_name = NULL;
    const char *production_date = NULL;
    const char *expiry_date = NULL;
    if (require_string_field(body, "sku", 64, &sku) != 0 ||
        require_string_field(body, "batch_no", 64, &batch_no) != 0 ||
        require_string_field(body, "supplier_name", 128, &supplier_name) != 0 ||
        require_string_field(body, "production_date", 32, &production_date) != 0 ||
        require_string_field(body, "expiry_date", 32, &expiry_date) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "sku/batch_no/supplier_name/production_date/expiry_date 必填");
    }

    int arrival_quantity = 0;
    int unit_cost = 0;
    if (parse_int_field(body, "arrival_quantity", 1, 1000000, &arrival_quantity) != 0 ||
        parse_int_field(body, "unit_cost_cents", 0, 100000000, &unit_cost) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "arrival_quantity/unit_cost_cents 必须为合法整数");
    }

    const char *note = optional_string_field(body, "note", 256);
    if (note == NULL) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "note 需为字符串且不超过256字符");
    }

    char sku_copy[65];
    char batch_no_copy[65];
    char supplier_name_copy[129];
    char production_date_copy[33];
    char expiry_date_copy[33];
    char note_copy[257];
    snprintf(sku_copy, sizeof(sku_copy), "%s", sku);
    snprintf(batch_no_copy, sizeof(batch_no_copy), "%s", batch_no);
    snprintf(supplier_name_copy, sizeof(supplier_name_copy), "%s", supplier_name);
    snprintf(production_date_copy, sizeof(production_date_copy), "%s", production_date);
    snprintf(expiry_date_copy, sizeof(expiry_date_copy), "%s", expiry_date);
    snprintf(note_copy, sizeof(note_copy), "%s", note ? note : "");

    pthread_mutex_lock(&g_db_mutex);

    AuthUser user;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    if (!authenticate_request(connection, &user, token_hash)) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_UNAUTHORIZED, "UNAUTHORIZED",
                            "需要登录");
    }

    if (!is_admin_role(&user)) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_FORBIDDEN, "FORBIDDEN",
                            "仅管理员可创建批次");
    }

    if (begin_transaction() != 0) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "开启事务失败");
    }

    sqlite3_stmt *stmt = NULL;
    int product_id = 0;

    const char *find_product_sql =
        "SELECT id FROM products WHERE sku = ? LIMIT 1;";
    if (sqlite3_prepare_v2(g_db, find_product_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询商品失败");
    }
    sqlite3_bind_text(stmt, 1, sku_copy, -1, SQLITE_TRANSIENT);
    int rc = sqlite3_step(stmt);
    if (rc != SQLITE_ROW) {
        sqlite3_finalize(stmt);
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_NOT_FOUND, "NOT_FOUND",
                            "商品不存在");
    }
    product_id = sqlite3_column_int(stmt, 0);
    sqlite3_finalize(stmt);

    int supplier_id = 0;
    const char *find_supplier_sql =
        "SELECT id FROM suppliers WHERE name = ? LIMIT 1;";
    if (sqlite3_prepare_v2(g_db, find_supplier_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询供应商失败");
    }
    sqlite3_bind_text(stmt, 1, supplier_name_copy, -1, SQLITE_TRANSIENT);
    rc = sqlite3_step(stmt);
    if (rc == SQLITE_ROW) {
        supplier_id = sqlite3_column_int(stmt, 0);
        sqlite3_finalize(stmt);
    } else {
        sqlite3_finalize(stmt);
        const char *ins_supplier_sql =
            "INSERT INTO suppliers (name) VALUES (?);";
        if (sqlite3_prepare_v2(g_db, ins_supplier_sql, -1, &stmt, NULL) != SQLITE_OK) {
            rollback_transaction();
            pthread_mutex_unlock(&g_db_mutex);
            json_decref(body);
            return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                                "DB_ERROR", "创建供应商失败");
        }
        sqlite3_bind_text(stmt, 1, supplier_name_copy, -1, SQLITE_TRANSIENT);
        rc = sqlite3_step(stmt);
        sqlite3_finalize(stmt);
        if (rc != SQLITE_DONE) {
            rollback_transaction();
            pthread_mutex_unlock(&g_db_mutex);
            json_decref(body);
            return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                                "DB_ERROR", "创建供应商失败");
        }
        supplier_id = (int)sqlite3_last_insert_rowid(g_db);
    }

    const char *ins_batch_sql =
        "INSERT INTO product_batches "
        "(product_id, batch_no, supplier_id, production_date, "
        "arrival_quantity, expiry_date, note) "
        "VALUES (?, ?, ?, ?, ?, ?, ?);";

    if (sqlite3_prepare_v2(g_db, ins_batch_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "创建批次失败");
    }

    sqlite3_bind_int(stmt, 1, product_id);
    sqlite3_bind_text(stmt, 2, batch_no_copy, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int(stmt, 3, supplier_id);
    sqlite3_bind_text(stmt, 4, production_date_copy, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int(stmt, 5, arrival_quantity);
    sqlite3_bind_text(stmt, 6, expiry_date_copy, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 7, note_copy, -1, SQLITE_TRANSIENT);

    rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);

    if (rc != SQLITE_DONE) {
        if (rc == SQLITE_CONSTRAINT) {
            rollback_transaction();
            pthread_mutex_unlock(&g_db_mutex);
            json_decref(body);
            return respond_error(connection, MHD_HTTP_CONFLICT, "CONFLICT",
                                "批次号已存在");
        }
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "创建批次失败");
    }

    int batch_id = (int)sqlite3_last_insert_rowid(g_db);

    const char *update_stock_sql =
        "UPDATE products SET stock_quantity = stock_quantity + ?, "
        "updated_at = CURRENT_TIMESTAMP WHERE id = ?;";
    if (sqlite3_prepare_v2(g_db, update_stock_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "更新库存失败");
    }
    sqlite3_bind_int(stmt, 1, arrival_quantity);
    sqlite3_bind_int(stmt, 2, product_id);
    rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);
    if (rc != SQLITE_DONE) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "更新库存失败");
    }

    const char *ins_movement_sql =
        "INSERT INTO stock_movements "
        "(product_id, movement_type, quantity, unit_price_cents, note, "
        "operator_user_id) "
        "VALUES (?, 'IN', ?, ?, ?, ?);";
    if (sqlite3_prepare_v2(g_db, ins_movement_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "写入流水失败");
    }
    sqlite3_bind_int(stmt, 1, product_id);
    sqlite3_bind_int(stmt, 2, arrival_quantity);
    sqlite3_bind_int(stmt, 3, unit_cost);
    sqlite3_bind_text(stmt, 4, note_copy, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int(stmt, 5, user.user_id);
    rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);

    if (rc != SQLITE_DONE || commit_transaction() != 0) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "提交批次入库事务失败");
    }

    pthread_mutex_unlock(&g_db_mutex);
    json_decref(body);

    json_t *data = json_object();
    json_object_set_new(data, "batch_id", json_integer(batch_id));
    json_object_set_new(data, "batch_no", json_string(batch_no_copy));
    json_object_set_new(data, "sku", json_string(sku_copy));
    json_object_set_new(data, "supplier", json_string(supplier_name_copy));
    json_object_set_new(data, "arrival_quantity", json_integer(arrival_quantity));
    return respond_success(connection, MHD_HTTP_CREATED, data);
}

static enum MHD_Result handle_list_batches(struct MHD_Connection *connection) {
    pthread_mutex_lock(&g_db_mutex);

    AuthUser user;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    if (!authenticate_request(connection, &user, token_hash)) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_UNAUTHORIZED, "UNAUTHORIZED",
                            "需要登录");
    }

    int limit = parse_limit_query(connection);

    sqlite3_stmt *stmt = NULL;
    const char *sql =
        "SELECT b.id, b.batch_no, p.sku, p.name, s.name as supplier_name, "
        "b.production_date, b.arrival_quantity, b.expiry_date, b.note, b.created_at "
        "FROM product_batches b "
        "JOIN products p ON p.id = b.product_id "
        "JOIN suppliers s ON s.id = b.supplier_id "
        "ORDER BY b.id DESC LIMIT ?;";

    if (sqlite3_prepare_v2(g_db, sql, -1, &stmt, NULL) != SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询批次列表失败");
    }

    sqlite3_bind_int(stmt, 1, limit);

    json_t *items = json_array();
    int rc = SQLITE_OK;
    while ((rc = sqlite3_step(stmt)) == SQLITE_ROW) {
        json_t *it = json_object();
        json_object_set_new(it, "id", json_integer(sqlite3_column_int(stmt, 0)));
        json_object_set_new(it, "batch_no", json_string(safe_col_text(stmt, 1)));
        json_object_set_new(it, "sku", json_string(safe_col_text(stmt, 2)));
        json_object_set_new(it, "product_name",
                            json_string(safe_col_text(stmt, 3)));
        json_object_set_new(it, "supplier_name",
                            json_string(safe_col_text(stmt, 4)));
        json_object_set_new(it, "production_date",
                            json_string(safe_col_text(stmt, 5)));
        json_object_set_new(it, "arrival_quantity",
                            json_integer(sqlite3_column_int(stmt, 6)));
        json_object_set_new(it, "expiry_date",
                            json_string(safe_col_text(stmt, 7)));
        json_object_set_new(it, "note", json_string(safe_col_text(stmt, 8)));
        json_object_set_new(it, "created_at",
                            json_string(safe_col_text(stmt, 9)));
        json_array_append_new(items, it);
    }

    sqlite3_finalize(stmt);
    pthread_mutex_unlock(&g_db_mutex);

    if (rc != SQLITE_DONE) {
        json_decref(items);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "读取批次列表失败");
    }

    return respond_success(connection, MHD_HTTP_OK, items);
}

static enum MHD_Result handle_place_batch(struct MHD_Connection *connection,
                                          ConnectionInfo *ci) {
    char err[256];
    json_t *body = NULL;
    if (parse_json_body(ci, &body, err) != 0) {
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_JSON", err);
    }

    const char *batch_no = NULL;
    const char *cabinet_code = NULL;
    if (require_string_field(body, "batch_no", 64, &batch_no) != 0 ||
        require_string_field(body, "cabinet_code", 32, &cabinet_code) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "batch_no/cabinet_code 必填");
    }

    int quantity = 0;
    if (parse_int_field(body, "quantity", 1, 1000000, &quantity) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "quantity 必须为合法正整数");
    }

    char batch_no_copy[65];
    char cabinet_code_copy[33];
    snprintf(batch_no_copy, sizeof(batch_no_copy), "%s", batch_no);
    snprintf(cabinet_code_copy, sizeof(cabinet_code_copy), "%s", cabinet_code);

    pthread_mutex_lock(&g_db_mutex);

    AuthUser user;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    if (!authenticate_request(connection, &user, token_hash)) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_UNAUTHORIZED, "UNAUTHORIZED",
                            "需要登录");
    }

    if (!is_admin_role(&user)) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_FORBIDDEN, "FORBIDDEN",
                            "仅管理员可入柜");
    }

    if (begin_transaction() != 0) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "开启事务失败");
    }

    sqlite3_stmt *stmt = NULL;
    int batch_id = 0;
    int arrival_quantity = 0;

    const char *find_batch_sql =
        "SELECT id, arrival_quantity FROM product_batches "
        "WHERE batch_no = ? LIMIT 1;";
    if (sqlite3_prepare_v2(g_db, find_batch_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询批次失败");
    }
    sqlite3_bind_text(stmt, 1, batch_no_copy, -1, SQLITE_TRANSIENT);
    int rc = sqlite3_step(stmt);
    if (rc != SQLITE_ROW) {
        sqlite3_finalize(stmt);
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_NOT_FOUND, "NOT_FOUND",
                            "批次不存在");
    }
    batch_id = sqlite3_column_int(stmt, 0);
    arrival_quantity = sqlite3_column_int(stmt, 1);
    sqlite3_finalize(stmt);

    int cabinet_id = 0;
    const char *find_cabinet_sql =
        "SELECT id FROM cabinets WHERE cabinet_code = ? LIMIT 1;";
    if (sqlite3_prepare_v2(g_db, find_cabinet_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询柜机失败");
    }
    sqlite3_bind_text(stmt, 1, cabinet_code_copy, -1, SQLITE_TRANSIENT);
    rc = sqlite3_step(stmt);
    if (rc != SQLITE_ROW) {
        sqlite3_finalize(stmt);
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_NOT_FOUND, "NOT_FOUND",
                            "柜机不存在");
    }
    cabinet_id = sqlite3_column_int(stmt, 0);
    sqlite3_finalize(stmt);

    int placed_quantity = 0;
    const char *sum_placed_sql =
        "SELECT COALESCE(SUM(current_quantity), 0) FROM cabinet_batch_stock "
        "WHERE batch_id = ?;";
    if (sqlite3_prepare_v2(g_db, sum_placed_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询已入柜数量失败");
    }
    sqlite3_bind_int(stmt, 1, batch_id);
    rc = sqlite3_step(stmt);
    if (rc == SQLITE_ROW) {
        placed_quantity = sqlite3_column_int(stmt, 0);
    }
    sqlite3_finalize(stmt);

    if (placed_quantity + quantity > arrival_quantity) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_CONFLICT, "INSUFFICIENT_BATCH",
                            "入柜数量超过批次到货数量");
    }

    const char *upsert_sql =
        "INSERT INTO cabinet_batch_stock (cabinet_id, batch_id, current_quantity) "
        "VALUES (?, ?, ?) "
        "ON CONFLICT(cabinet_id, batch_id) DO UPDATE SET "
        "current_quantity = current_quantity + ?, "
        "updated_at = CURRENT_TIMESTAMP;";
    if (sqlite3_prepare_v2(g_db, upsert_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "更新柜机批次库存失败");
    }
    sqlite3_bind_int(stmt, 1, cabinet_id);
    sqlite3_bind_int(stmt, 2, batch_id);
    sqlite3_bind_int(stmt, 3, quantity);
    sqlite3_bind_int(stmt, 4, quantity);
    rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);

    if (rc != SQLITE_DONE || commit_transaction() != 0) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "提交入柜事务失败");
    }

    pthread_mutex_unlock(&g_db_mutex);
    json_decref(body);

    json_t *data = json_object();
    json_object_set_new(data, "batch_no", json_string(batch_no_copy));
    json_object_set_new(data, "cabinet_code", json_string(cabinet_code_copy));
    json_object_set_new(data, "quantity", json_integer(quantity));
    return respond_success(connection, MHD_HTTP_OK, data);
}

static int generate_order_no(char *out, size_t out_size) {
    time_t t = now_epoch();
    struct tm tm_info;
    localtime_r(&t, &tm_info);

    char prefix[32];
    strftime(prefix, sizeof(prefix), "ORD%Y%m%d%H%M%S", &tm_info);

    unsigned char rand_bytes[4];
    randombytes_buf(rand_bytes, sizeof(rand_bytes));
    char rand_hex[9];
    bytes_to_hex(rand_bytes, sizeof(rand_bytes), rand_hex);

    snprintf(out, out_size, "%s%s", prefix, rand_hex);
    return 0;
}

static enum MHD_Result handle_cabinet_sales(struct MHD_Connection *connection,
                                            ConnectionInfo *ci) {
    char err[256];
    json_t *body = NULL;
    if (parse_json_body(ci, &body, err) != 0) {
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_JSON", err);
    }

    const char *cabinet_code = NULL;
    const char *batch_no = NULL;
    if (require_string_field(body, "cabinet_code", 32, &cabinet_code) != 0 ||
        require_string_field(body, "batch_no", 64, &batch_no) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "cabinet_code/batch_no 必填");
    }

    int quantity = 0;
    int unit_price = 0;
    if (parse_int_field(body, "quantity", 1, 1000000, &quantity) != 0 ||
        parse_int_field(body, "unit_price_cents", 0, 100000000, &unit_price) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "quantity/unit_price_cents 必须为合法整数");
    }

    const char *note = optional_string_field(body, "note", 256);
    if (note == NULL) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "note 需为字符串且不超过256字符");
    }

    char cabinet_code_copy[33];
    char batch_no_copy[65];
    char note_copy[257];
    snprintf(cabinet_code_copy, sizeof(cabinet_code_copy), "%s", cabinet_code);
    snprintf(batch_no_copy, sizeof(batch_no_copy), "%s", batch_no);
    snprintf(note_copy, sizeof(note_copy), "%s", note ? note : "");

    int total_price = quantity * unit_price;

    pthread_mutex_lock(&g_db_mutex);

    AuthUser user;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    if (!authenticate_request(connection, &user, token_hash)) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_UNAUTHORIZED, "UNAUTHORIZED",
                            "需要登录");
    }

    if (begin_transaction() != 0) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "开启事务失败");
    }

    sqlite3_stmt *stmt = NULL;
    int cabinet_id = 0;
    int batch_id = 0;
    int product_id = 0;
    int current_qty = 0;

    const char *find_sql =
        "SELECT c.id, b.id, b.product_id, s.current_quantity "
        "FROM cabinet_batch_stock s "
        "JOIN cabinets c ON c.id = s.cabinet_id "
        "JOIN product_batches b ON b.id = s.batch_id "
        "WHERE c.cabinet_code = ? AND b.batch_no = ? LIMIT 1;";
    if (sqlite3_prepare_v2(g_db, find_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询柜机批次库存失败");
    }
    sqlite3_bind_text(stmt, 1, cabinet_code_copy, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 2, batch_no_copy, -1, SQLITE_TRANSIENT);
    int rc = sqlite3_step(stmt);
    if (rc != SQLITE_ROW) {
        sqlite3_finalize(stmt);
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_NOT_FOUND, "NOT_FOUND",
                            "柜机中无该批次库存");
    }
    cabinet_id = sqlite3_column_int(stmt, 0);
    batch_id = sqlite3_column_int(stmt, 1);
    product_id = sqlite3_column_int(stmt, 2);
    current_qty = sqlite3_column_int(stmt, 3);
    sqlite3_finalize(stmt);

    if (current_qty < quantity) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_CONFLICT, "INSUFFICIENT_STOCK",
                            "柜机批次库存不足");
    }

    const char *update_stock_sql =
        "UPDATE cabinet_batch_stock SET current_quantity = current_quantity - ?, "
        "updated_at = CURRENT_TIMESTAMP "
        "WHERE cabinet_id = ? AND batch_id = ?;";
    if (sqlite3_prepare_v2(g_db, update_stock_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "更新柜机库存失败");
    }
    sqlite3_bind_int(stmt, 1, quantity);
    sqlite3_bind_int(stmt, 2, cabinet_id);
    sqlite3_bind_int(stmt, 3, batch_id);
    rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);
    if (rc != SQLITE_DONE) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "更新柜机库存失败");
    }

    const char *update_product_sql =
        "UPDATE products SET stock_quantity = stock_quantity - ?, "
        "updated_at = CURRENT_TIMESTAMP WHERE id = ?;";
    if (sqlite3_prepare_v2(g_db, update_product_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "更新商品库存失败");
    }
    sqlite3_bind_int(stmt, 1, quantity);
    sqlite3_bind_int(stmt, 2, product_id);
    rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);
    if (rc != SQLITE_DONE) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "更新商品库存失败");
    }

    const char *ins_movement_sql =
        "INSERT INTO stock_movements "
        "(product_id, movement_type, quantity, unit_price_cents, note, "
        "operator_user_id) "
        "VALUES (?, 'OUT', ?, ?, ?, ?);";
    if (sqlite3_prepare_v2(g_db, ins_movement_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "写入流水失败");
    }
    sqlite3_bind_int(stmt, 1, product_id);
    sqlite3_bind_int(stmt, 2, quantity);
    sqlite3_bind_int(stmt, 3, unit_price);
    sqlite3_bind_text(stmt, 4, note_copy, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int(stmt, 5, user.user_id);
    rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);
    if (rc != SQLITE_DONE) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "写入流水失败");
    }

    char order_no[64];
    generate_order_no(order_no, sizeof(order_no));

    const char *ins_order_sql =
        "INSERT INTO sales_orders "
        "(order_no, cabinet_id, batch_id, product_id, quantity, "
        "unit_price_cents, total_price_cents, note) "
        "VALUES (?, ?, ?, ?, ?, ?, ?, ?);";
    if (sqlite3_prepare_v2(g_db, ins_order_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "创建订单失败");
    }
    sqlite3_bind_text(stmt, 1, order_no, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int(stmt, 2, cabinet_id);
    sqlite3_bind_int(stmt, 3, batch_id);
    sqlite3_bind_int(stmt, 4, product_id);
    sqlite3_bind_int(stmt, 5, quantity);
    sqlite3_bind_int(stmt, 6, unit_price);
    sqlite3_bind_int(stmt, 7, total_price);
    sqlite3_bind_text(stmt, 8, note_copy, -1, SQLITE_TRANSIENT);
    rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);

    if (rc != SQLITE_DONE || commit_transaction() != 0) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "提交销售事务失败");
    }

    pthread_mutex_unlock(&g_db_mutex);
    json_decref(body);

    json_t *data = json_object();
    json_object_set_new(data, "order_no", json_string(order_no));
    json_object_set_new(data, "cabinet_code", json_string(cabinet_code_copy));
    json_object_set_new(data, "batch_no", json_string(batch_no_copy));
    json_object_set_new(data, "quantity", json_integer(quantity));
    json_object_set_new(data, "total_price_cents", json_integer(total_price));
    return respond_success(connection, MHD_HTTP_OK, data);
}

static enum MHD_Result handle_recall_query(struct MHD_Connection *connection) {
    pthread_mutex_lock(&g_db_mutex);

    AuthUser user;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    if (!authenticate_request(connection, &user, token_hash)) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_UNAUTHORIZED, "UNAUTHORIZED",
                            "需要登录");
    }

    if (!is_admin_role(&user)) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_FORBIDDEN, "FORBIDDEN",
                            "仅管理员可查询召回信息");
    }

    const char *batch_no =
        MHD_lookup_connection_value(connection, MHD_GET_ARGUMENT_KIND, "batch_no");
    const char *supplier_name =
        MHD_lookup_connection_value(connection, MHD_GET_ARGUMENT_KIND, "supplier_name");
    const char *production_date_from =
        MHD_lookup_connection_value(connection, MHD_GET_ARGUMENT_KIND, "production_date_from");
    const char *production_date_to =
        MHD_lookup_connection_value(connection, MHD_GET_ARGUMENT_KIND, "production_date_to");

    int has_filter = 0;
    char where_clause[512] = {0};
    strcat(where_clause, "WHERE 1=1");

    if (batch_no != NULL && *batch_no != '\0') {
        strcat(where_clause, " AND b.batch_no = ?");
        has_filter = 1;
    }
    if (supplier_name != NULL && *supplier_name != '\0') {
        strcat(where_clause, " AND s.name = ?");
        has_filter = 1;
    }
    if (production_date_from != NULL && *production_date_from != '\0') {
        strcat(where_clause, " AND b.production_date >= ?");
        has_filter = 1;
    }
    if (production_date_to != NULL && *production_date_to != '\0') {
        strcat(where_clause, " AND b.production_date <= ?");
        has_filter = 1;
    }

    if (!has_filter) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "请至少提供一个查询条件：batch_no / supplier_name / production_date_from / production_date_to");
    }

    sqlite3_stmt *stmt = NULL;

    char batch_sql[1024];
    snprintf(batch_sql, sizeof(batch_sql),
        "SELECT DISTINCT b.id, b.batch_no, p.sku, p.name, s.name as supplier_name, "
        "b.production_date, b.arrival_quantity, b.expiry_date "
        "FROM product_batches b "
        "JOIN products p ON p.id = b.product_id "
        "JOIN suppliers s ON s.id = b.supplier_id "
        "%s "
        "ORDER BY b.id DESC;",
        where_clause);

    if (sqlite3_prepare_v2(g_db, batch_sql, -1, &stmt, NULL) != SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询召回批次失败");
    }

    int bind_idx = 1;
    if (batch_no != NULL && *batch_no != '\0') {
        sqlite3_bind_text(stmt, bind_idx++, batch_no, -1, SQLITE_TRANSIENT);
    }
    if (supplier_name != NULL && *supplier_name != '\0') {
        sqlite3_bind_text(stmt, bind_idx++, supplier_name, -1, SQLITE_TRANSIENT);
    }
    if (production_date_from != NULL && *production_date_from != '\0') {
        sqlite3_bind_text(stmt, bind_idx++, production_date_from, -1, SQLITE_TRANSIENT);
    }
    if (production_date_to != NULL && *production_date_to != '\0') {
        sqlite3_bind_text(stmt, bind_idx++, production_date_to, -1, SQLITE_TRANSIENT);
    }

    json_t *batches = json_array();
    int batch_count = 0;
    int total_unsold = 0;
    int total_sold = 0;

    int *batch_ids = NULL;
    size_t batch_ids_size = 0;
    size_t batch_ids_cap = 16;
    batch_ids = (int *)malloc(batch_ids_cap * sizeof(int));
    if (batch_ids == NULL) {
        sqlite3_finalize(stmt);
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(batches);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "MEMORY_ERROR", "内存分配失败");
    }

    int rc = SQLITE_OK;
    while ((rc = sqlite3_step(stmt)) == SQLITE_ROW) {
        if (batch_ids_size >= batch_ids_cap) {
            batch_ids_cap *= 2;
            int *tmp = (int *)realloc(batch_ids, batch_ids_cap * sizeof(int));
            if (tmp == NULL) {
                free(batch_ids);
                sqlite3_finalize(stmt);
                pthread_mutex_unlock(&g_db_mutex);
                json_decref(batches);
                return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                                    "MEMORY_ERROR", "内存分配失败");
            }
            batch_ids = tmp;
        }
        batch_ids[batch_ids_size++] = sqlite3_column_int(stmt, 0);

        json_t *it = json_object();
        json_object_set_new(it, "id", json_integer(sqlite3_column_int(stmt, 0)));
        json_object_set_new(it, "batch_no", json_string(safe_col_text(stmt, 1)));
        json_object_set_new(it, "sku", json_string(safe_col_text(stmt, 2)));
        json_object_set_new(it, "product_name",
                            json_string(safe_col_text(stmt, 3)));
        json_object_set_new(it, "supplier_name",
                            json_string(safe_col_text(stmt, 4)));
        json_object_set_new(it, "production_date",
                            json_string(safe_col_text(stmt, 5)));
        json_object_set_new(it, "arrival_quantity",
                            json_integer(sqlite3_column_int(stmt, 6)));
        json_object_set_new(it, "expiry_date",
                            json_string(safe_col_text(stmt, 7)));
        json_array_append_new(batches, it);
        batch_count++;
    }
    sqlite3_finalize(stmt);

    if (rc != SQLITE_DONE) {
        free(batch_ids);
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(batches);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "读取召回批次失败");
    }

    json_t *affected_cabinets = json_array();
    json_t *orders = json_array();

    if (batch_ids_size > 0) {
        char batch_id_list[1024] = {0};
        for (size_t i = 0; i < batch_ids_size; ++i) {
            char buf[16];
            snprintf(buf, sizeof(buf), "%s%d",
                     i == 0 ? "" : ",", batch_ids[i]);
            strncat(batch_id_list, buf,
                    sizeof(batch_id_list) - strlen(batch_id_list) - 1);
        }

        char cabinet_sql[1024];
        snprintf(cabinet_sql, sizeof(cabinet_sql),
            "SELECT c.id, c.cabinet_code, c.name, c.location, "
            "SUM(s.current_quantity) as unsold_quantity "
            "FROM cabinet_batch_stock s "
            "JOIN cabinets c ON c.id = s.cabinet_id "
            "WHERE s.batch_id IN (%s) AND s.current_quantity > 0 "
            "GROUP BY c.id, c.cabinet_code, c.name, c.location "
            "ORDER BY c.id;",
            batch_id_list);

        if (sqlite3_prepare_v2(g_db, cabinet_sql, -1, &stmt, NULL) != SQLITE_OK) {
            free(batch_ids);
            pthread_mutex_unlock(&g_db_mutex);
            json_decref(batches);
            json_decref(affected_cabinets);
            json_decref(orders);
            return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                                "DB_ERROR", "查询受影响柜机失败");
        }

        while ((rc = sqlite3_step(stmt)) == SQLITE_ROW) {
            int qty = sqlite3_column_int(stmt, 4);
            total_unsold += qty;
            json_t *it = json_object();
            json_object_set_new(it, "id",
                                json_integer(sqlite3_column_int(stmt, 0)));
            json_object_set_new(it, "cabinet_code",
                                json_string(safe_col_text(stmt, 1)));
            json_object_set_new(it, "name",
                                json_string(safe_col_text(stmt, 2)));
            json_object_set_new(it, "location",
                                json_string(safe_col_text(stmt, 3)));
            json_object_set_new(it, "unsold_quantity", json_integer(qty));
            json_array_append_new(affected_cabinets, it);
        }
        sqlite3_finalize(stmt);

        char order_sql[1024];
        snprintf(order_sql, sizeof(order_sql),
            "SELECT o.id, o.order_no, c.cabinet_code, c.name as cabinet_name, "
            "b.batch_no, p.sku, p.name as product_name, "
            "o.quantity, o.unit_price_cents, o.total_price_cents, "
            "o.created_at "
            "FROM sales_orders o "
            "JOIN cabinets c ON c.id = o.cabinet_id "
            "JOIN product_batches b ON b.id = o.batch_id "
            "JOIN products p ON p.id = o.product_id "
            "WHERE o.batch_id IN (%s) "
            "ORDER BY o.id DESC LIMIT 500;",
            batch_id_list);

        if (sqlite3_prepare_v2(g_db, order_sql, -1, &stmt, NULL) != SQLITE_OK) {
            free(batch_ids);
            pthread_mutex_unlock(&g_db_mutex);
            json_decref(batches);
            json_decref(affected_cabinets);
            json_decref(orders);
            return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                                "DB_ERROR", "查询销售订单失败");
        }

        while ((rc = sqlite3_step(stmt)) == SQLITE_ROW) {
            total_sold += sqlite3_column_int(stmt, 7);
            json_t *it = json_object();
            json_object_set_new(it, "id",
                                json_integer(sqlite3_column_int(stmt, 0)));
            json_object_set_new(it, "order_no",
                                json_string(safe_col_text(stmt, 1)));
            json_object_set_new(it, "cabinet_code",
                                json_string(safe_col_text(stmt, 2)));
            json_object_set_new(it, "cabinet_name",
                                json_string(safe_col_text(stmt, 3)));
            json_object_set_new(it, "batch_no",
                                json_string(safe_col_text(stmt, 4)));
            json_object_set_new(it, "sku", json_string(safe_col_text(stmt, 5)));
            json_object_set_new(it, "product_name",
                                json_string(safe_col_text(stmt, 6)));
            json_object_set_new(it, "quantity",
                                json_integer(sqlite3_column_int(stmt, 7)));
            json_object_set_new(it, "unit_price_cents",
                                json_integer(sqlite3_column_int(stmt, 8)));
            json_object_set_new(it, "total_price_cents",
                                json_integer(sqlite3_column_int(stmt, 9)));
            json_object_set_new(it, "created_at",
                                json_string(safe_col_text(stmt, 10)));
            json_array_append_new(orders, it);
        }
        sqlite3_finalize(stmt);
    }

    free(batch_ids);
    pthread_mutex_unlock(&g_db_mutex);

    json_t *data = json_object();
    json_object_set_new(data, "affected_batch_count", json_integer(batch_count));
    json_object_set_new(data, "total_unsold_quantity", json_integer(total_unsold));
    json_object_set_new(data, "total_sold_quantity", json_integer(total_sold));
    json_object_set_new(data, "affected_batches", batches);
    json_object_set_new(data, "affected_cabinets", affected_cabinets);
    json_object_set_new(data, "sold_orders", orders);

    return respond_success(connection, MHD_HTTP_OK, data);
}

static enum MHD_Result route_health(struct MHD_Connection *connection,
                                    ConnectionInfo *ci) {
    (void)ci;
    return handle_health(connection);
}

static enum MHD_Result route_register(struct MHD_Connection *connection,
                                      ConnectionInfo *ci) {
    return handle_register(connection, ci);
}

static enum MHD_Result route_login(struct MHD_Connection *connection,
                                   ConnectionInfo *ci) {
    return handle_login(connection, ci);
}

static enum MHD_Result route_logout(struct MHD_Connection *connection,
                                    ConnectionInfo *ci) {
    (void)ci;
    return handle_logout(connection);
}

static enum MHD_Result route_auth_me(struct MHD_Connection *connection,
                                     ConnectionInfo *ci) {
    (void)ci;
    return handle_auth_me(connection);
}

static enum MHD_Result route_create_product(struct MHD_Connection *connection,
                                            ConnectionInfo *ci) {
    return handle_create_product(connection, ci);
}

static enum MHD_Result route_list_products(struct MHD_Connection *connection,
                                           ConnectionInfo *ci) {
    (void)ci;
    return handle_list_products(connection);
}

static enum MHD_Result route_inbound(struct MHD_Connection *connection,
                                     ConnectionInfo *ci) {
    return handle_inbound(connection, ci);
}

static enum MHD_Result route_sales(struct MHD_Connection *connection,
                                   ConnectionInfo *ci) {
    return handle_sales(connection, ci);
}

static enum MHD_Result route_inventory(struct MHD_Connection *connection,
                                       ConnectionInfo *ci) {
    (void)ci;
    return handle_inventory(connection);
}

static enum MHD_Result route_movements(struct MHD_Connection *connection,
                                       ConnectionInfo *ci) {
    (void)ci;
    return handle_movements(connection);
}

static enum MHD_Result route_create_supplier(struct MHD_Connection *connection,
                                             ConnectionInfo *ci) {
    return handle_create_supplier(connection, ci);
}

static enum MHD_Result route_list_suppliers(struct MHD_Connection *connection,
                                            ConnectionInfo *ci) {
    (void)ci;
    return handle_list_suppliers(connection);
}

static enum MHD_Result route_create_cabinet(struct MHD_Connection *connection,
                                            ConnectionInfo *ci) {
    return handle_create_cabinet(connection, ci);
}

static enum MHD_Result route_list_cabinets(struct MHD_Connection *connection,
                                           ConnectionInfo *ci) {
    (void)ci;
    return handle_list_cabinets(connection);
}

static enum MHD_Result route_create_batch(struct MHD_Connection *connection,
                                          ConnectionInfo *ci) {
    return handle_create_batch(connection, ci);
}

static enum MHD_Result route_list_batches(struct MHD_Connection *connection,
                                          ConnectionInfo *ci) {
    (void)ci;
    return handle_list_batches(connection);
}

static enum MHD_Result route_place_batch(struct MHD_Connection *connection,
                                         ConnectionInfo *ci) {
    return handle_place_batch(connection, ci);
}

static enum MHD_Result route_cabinet_sales(struct MHD_Connection *connection,
                                           ConnectionInfo *ci) {
    return handle_cabinet_sales(connection, ci);
}

static enum MHD_Result route_recall_query(struct MHD_Connection *connection,
                                          ConnectionInfo *ci) {
    (void)ci;
    return handle_recall_query(connection);
}

static enum MHD_Result route_openapi_doc(struct MHD_Connection *connection,
                                         ConnectionInfo *ci);

static enum MHD_Result route_swagger_ui(struct MHD_Connection *connection,
                                        ConnectionInfo *ci) {
    (void)ci;
    return docs_send_swagger_ui(connection);
}

static enum MHD_Result route_home(struct MHD_Connection *connection,
                                  ConnectionInfo *ci) {
    (void)ci;
    return docs_send_home(connection);
}

static const ApiRoute g_api_routes[] = {
    {MHD_HTTP_METHOD_GET, "/", route_home, "Home", "服务首页", "System", 0, 0, 0},
    {MHD_HTTP_METHOD_GET, "/api/v1/health", route_health, "Health Check",
     "服务健康检查", "System", 0, 0, 1},
    {MHD_HTTP_METHOD_POST, "/api/v1/auth/register", route_register, "Create User",
     "创建用户（需管理员鉴权）", "Auth", 1, 1, 1},
    {MHD_HTTP_METHOD_POST, "/api/v1/auth/login", route_login, "Login",
     "用户登录并获取访问令牌", "Auth", 0, 1, 1},
    {MHD_HTTP_METHOD_POST, "/api/v1/auth/logout", route_logout, "Logout",
     "当前令牌退出登录", "Auth", 1, 0, 1},
    {MHD_HTTP_METHOD_GET, "/api/v1/auth/me", route_auth_me, "Current User",
     "获取当前登录用户信息", "Auth", 1, 0, 1},
    {MHD_HTTP_METHOD_POST, "/api/v1/products", route_create_product,
     "Create Product", "新增商品（管理员）", "Product", 1, 1, 1},
    {MHD_HTTP_METHOD_GET, "/api/v1/products", route_list_products, "List Products",
     "查询商品列表", "Product", 0, 0, 1},
    {MHD_HTTP_METHOD_POST, "/api/v1/inbound", route_inbound, "Inbound",
     "入库（进货）", "Inventory", 1, 1, 1},
    {MHD_HTTP_METHOD_POST, "/api/v1/sales", route_sales, "Sales",
     "销售出库", "Inventory", 1, 1, 1},
    {MHD_HTTP_METHOD_GET, "/api/v1/inventory", route_inventory, "Inventory Summary",
     "库存汇总与明细", "Inventory", 0, 0, 1},
    {MHD_HTTP_METHOD_GET, "/api/v1/movements", route_movements, "Movement History",
     "库存流水查询", "Inventory", 1, 0, 1},
    {MHD_HTTP_METHOD_POST, "/api/v1/suppliers", route_create_supplier,
     "Create Supplier", "新增供应商（管理员）", "Batch", 1, 1, 1},
    {MHD_HTTP_METHOD_GET, "/api/v1/suppliers", route_list_suppliers,
     "List Suppliers", "查询供应商列表", "Batch", 1, 0, 1},
    {MHD_HTTP_METHOD_POST, "/api/v1/cabinets", route_create_cabinet,
     "Create Cabinet", "新增柜机（管理员）", "Batch", 1, 1, 1},
    {MHD_HTTP_METHOD_GET, "/api/v1/cabinets", route_list_cabinets,
     "List Cabinets", "查询柜机列表", "Batch", 1, 0, 1},
    {MHD_HTTP_METHOD_POST, "/api/v1/batches", route_create_batch,
     "Create Batch", "创建批次（批次入库）", "Batch", 1, 1, 1},
    {MHD_HTTP_METHOD_GET, "/api/v1/batches", route_list_batches,
     "List Batches", "查询批次列表", "Batch", 1, 0, 1},
    {MHD_HTTP_METHOD_POST, "/api/v1/batch-placements", route_place_batch,
     "Place Batch", "批次入柜（分配到柜机）", "Batch", 1, 1, 1},
    {MHD_HTTP_METHOD_POST, "/api/v1/cabinet-sales", route_cabinet_sales,
     "Cabinet Sales", "柜机销售（带批次追溯）", "Batch", 1, 1, 1},
    {MHD_HTTP_METHOD_GET, "/api/v1/recall", route_recall_query,
     "Recall Query", "召回查询（受影响柜机/库存/订单）", "Batch", 1, 0, 1},
    {MHD_HTTP_METHOD_GET, "/api/v1/openapi.json", route_openapi_doc,
     "OpenAPI Document", "自动生成的 OpenAPI 文档", "System", 0, 0, 1},
    {MHD_HTTP_METHOD_GET, "/docs", route_swagger_ui, "Swagger UI",
     "Swagger 交互式文档页面", "System", 0, 0, 1},
};

static const size_t g_api_routes_count =
    sizeof(g_api_routes) / sizeof(g_api_routes[0]);

static enum MHD_Result route_openapi_doc(struct MHD_Connection *connection,
                                         ConnectionInfo *ci) {
    (void)ci;
    return docs_send_openapi(connection, g_api_routes, g_api_routes_count);
}

static enum MHD_Result handle_options(struct MHD_Connection *connection) {
    struct MHD_Response *response =
        MHD_create_response_from_buffer(0, "", MHD_RESPMEM_PERSISTENT);
    if (response == NULL) {
        return MHD_NO;
    }

    MHD_add_response_header(response, "Access-Control-Allow-Origin", "*");
    MHD_add_response_header(response, "Access-Control-Allow-Headers",
                            "Content-Type, Authorization");
    MHD_add_response_header(response, "Access-Control-Allow-Methods",
                            "GET, POST, OPTIONS");

    enum MHD_Result ret = MHD_queue_response(connection, MHD_HTTP_NO_CONTENT, response);
    MHD_destroy_response(response);
    return ret;
}

static enum MHD_Result route_request(struct MHD_Connection *connection,
                                     const char *url, const char *method,
                                     ConnectionInfo *ci) {
    if (strcmp(method, MHD_HTTP_METHOD_OPTIONS) == 0) {
        return handle_options(connection);
    }

    for (size_t i = 0; i < g_api_routes_count; ++i) {
        if (strcmp(method, g_api_routes[i].method) == 0 &&
            strcmp(url, g_api_routes[i].path) == 0) {
            return g_api_routes[i].handler(connection, ci);
        }
    }

    return respond_error(connection, MHD_HTTP_NOT_FOUND, "NOT_FOUND", "接口不存在");
}

static enum MHD_Result request_handler(void *cls,
                                       struct MHD_Connection *connection,
                                       const char *url, const char *method,
                                       const char *version,
                                       const char *upload_data,
                                       size_t *upload_data_size, void **con_cls) {
    (void)cls;
    (void)version;

    ConnectionInfo *ci = (ConnectionInfo *)(*con_cls);
    if (ci == NULL) {
        ci = (ConnectionInfo *)calloc(1, sizeof(ConnectionInfo));
        if (ci == NULL) {
            return MHD_NO;
        }
        *con_cls = ci;
        return MHD_YES;
    }

    if (is_method_with_body(method) && *upload_data_size != 0) {
        if (append_body(ci, upload_data, *upload_data_size) != 0) {
            *upload_data_size = 0;
            return respond_error(connection, MHD_HTTP_CONTENT_TOO_LARGE,
                                "PAYLOAD_TOO_LARGE", "请求体超过限制");
        }

        *upload_data_size = 0;
        return MHD_YES;
    }

    if (ci->processed) {
        return MHD_YES;
    }
    ci->processed = 1;

    return route_request(connection, url, method, ci);
}

static void request_completed_callback(void *cls, struct MHD_Connection *connection,
                                       void **con_cls,
                                       enum MHD_RequestTerminationCode toe) {
    (void)cls;
    (void)connection;
    (void)toe;

    ConnectionInfo *ci = (ConnectionInfo *)(*con_cls);
    if (ci != NULL) {
        free(ci->body);
        free(ci);
        *con_cls = NULL;
    }
}

static void load_config(void) {
    g_cfg.port = env_to_int("PORT", DEFAULT_PORT);
    g_cfg.session_ttl_hours =
        env_to_int("SESSION_TTL_HOURS", DEFAULT_SESSION_TTL_HOURS);
    g_cfg.db_path = getenv("DB_PATH");
    if (g_cfg.db_path == NULL || *g_cfg.db_path == '\0') {
        g_cfg.db_path = DEFAULT_DB_PATH;
    }

    g_cfg.key_file = getenv("USER_DATA_KEY_FILE");
    if (g_cfg.key_file == NULL || *g_cfg.key_file == '\0') {
        g_cfg.key_file = DEFAULT_KEY_FILE;
    }
}

int main(void) {
    signal(SIGINT, handle_signal);
    signal(SIGTERM, handle_signal);

    load_config();

    if (sodium_init() < 0) {
        fprintf(stderr, "[FATAL] libsodium 初始化失败\n");
        return 1;
    }

    if (db_init() != 0) {
        fprintf(stderr, "[FATAL] 数据库初始化失败\n");
        return 1;
    }

    if (load_or_create_key() != 0) {
        fprintf(stderr, "[FATAL] 用户字段加密密钥初始化失败\n");
        sqlite3_close(g_db);
        return 1;
    }

    if (ensure_default_admin_user() != 0) {
        fprintf(stderr, "[FATAL] 默认管理员初始化失败\n");
        sqlite3_close(g_db);
        return 1;
    }

    if (ensure_seed_stock_movement_consistency() != 0) {
        fprintf(stderr, "[FATAL] 种子库存流水修复失败\n");
        sqlite3_close(g_db);
        return 1;
    }

    struct MHD_Daemon *daemon = MHD_start_daemon(
        MHD_USE_INTERNAL_POLLING_THREAD, (uint16_t)g_cfg.port, NULL, NULL,
        &request_handler, NULL, MHD_OPTION_NOTIFY_COMPLETED,
        request_completed_callback, NULL, MHD_OPTION_END);

    if (daemon == NULL) {
        fprintf(stderr, "[FATAL] HTTP 服务启动失败\n");
        sqlite3_close(g_db);
        return 1;
    }

    fprintf(stdout,
            "[INFO] 服务启动成功\n"
            "[INFO] 端口: %d\n"
            "[INFO] 数据库: %s\n"
            "[INFO] 会话时长(小时): %d\n",
            g_cfg.port, g_cfg.db_path, g_cfg.session_ttl_hours);

    while (g_running) {
        sleep(1);
    }

    MHD_stop_daemon(daemon);
    sqlite3_close(g_db);
    pthread_mutex_destroy(&g_db_mutex);

    fprintf(stdout, "[INFO] 服务已停止\n");
    return 0;
}
