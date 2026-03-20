/*
COMPILE: gcc -O3 -s -lm -pthread chess.c -o chess
   TT_SIZE LOOKUP TABLE (STRICTLY POWER OF 2 ENTRIES)
   Formula: Entries = (Bytes * 1024) / 8 bytes per entry
   WARNING: Memory Usage = TT_SIZE * 8 bytes * NUMBER_OF_THREADS
            With 12 threads, 128 MB/table = 1.5 GB Total RAM.
            With 12 threads, 16 GB/table = 192 GB Total RAM (WILL CRASH MOST PCS).
   Format: [TABLE_SIZE_KB/MB/GB]:   #define TT_SIZE [TABLE_SIZE]
   --- SUPER LOW MEMORY OPTIONS (B) ---
   64 B:   #define TT_SIZE 8
   128 B:  #define TT_SIZE 16
   256 B:  #define TT_SIZE 32
   512 B:  #define TT_SIZE 64
   
   --- LOW MEMORY OPTIONS (KB) ---
   1 KB:   #define TT_SIZE 128
   2 KB:   #define TT_SIZE 256          
   4 KB:   #define TT_SIZE 512          
   8 KB:   #define TT_SIZE 1024         
   16 KB:  #define TT_SIZE 2048         
   32 KB:  #define TT_SIZE 4096         
   64 KB:  #define TT_SIZE 8192         
   128 KB: #define TT_SIZE 16384        
   256 KB: #define TT_SIZE 32768        
   512 KB: #define TT_SIZE 65536        
   1 MB:   #define TT_SIZE 131072       

   --- SAFE FOR MOST LAPTOPS (Total RAM < 4GB) ---
   2 MB:   #define TT_SIZE 262144       
   4 MB:   #define TT_SIZE 524288       
   8 MB:   #define TT_SIZE 1048576      
   16 MB:  #define TT_SIZE 2097152      
   32 MB:  #define TT_SIZE 4194304      
   64 MB:  #define TT_SIZE 8388608      
   128 MB: #define TT_SIZE 16777216     
   256 MB: #define TT_SIZE 33554432     
   512 MB: #define TT_SIZE 67108864     
   1024 MB:#define TT_SIZE 134217728    

   --- DANGEROUS ZONE (REQUIRES MASSIVE RAM) ---
   2 GB:   #define TT_SIZE 268435456    
   4 GB:   #define TT_SIZE 536870912    
   8 GB:   #define TT_SIZE 1073741824   
   16 GB:  #define TT_SIZE 2147483648   

   NOTE: Always use powers of 2 for bitwise AND speed (key & (TT_SIZE - 1)).
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <stdint.h>
#include <time.h>
#include <math.h>
#include <ctype.h>
#include <pthread.h>
#include <stdatomic.h>

#ifdef _WIN32
#include <windows.h>
#include <sysinfoapi.h>
static int get_cpu_count() {
    SYSTEM_INFO sysinfo;
    GetSystemInfo(&sysinfo);
    return sysinfo.dwNumberOfProcessors;
}
static void sleep_ms(int ms) {
    Sleep(ms);
}
#else
#include <unistd.h>
static int get_cpu_count() {
    int count = sysconf(_SC_NPROCESSORS_ONLN);
    return count > 0 ? count : 1;
}
static void sleep_ms(int ms) {
    usleep(ms * 1000);
}
#endif

#define MAX_THREADS 256
#define TT_SIZE 67108864
#define EMPTY 0
#define WHITE 1
#define BLACK 2
#define P 1
#define N 2
#define B 3
#define R 4
#define Q 5
#define K 6
int debug_pvs = 0;

#define BOARD_SIZE 64
#define MAX_MOVES 256
#define INF 32000
#define MATE_SCORE 30000

typedef struct {
    uint8_t from;
    uint8_t to;
    uint8_t captured;
    uint8_t flags;  
} Move;

typedef struct {
    uint8_t squares[BOARD_SIZE];
} Board;

typedef struct {
    uint32_t key;       
    int16_t eval;       
    uint8_t depth;
    uint8_t flag;
} TTEntry;

typedef struct {
    _Atomic(uint64_t) data;
} LockFreeTTEntry;

typedef struct {
    LockFreeTTEntry entries[TT_SIZE];
} TranspositionTable;

int num_threads = 1;
TranspositionTable* shared_tt = NULL;
pthread_t thread_pool[MAX_THREADS];

#define KILLER_DEPTH 64
__thread int killer_moves[KILLER_DEPTH][2];

uint32_t zobrist_table[BOARD_SIZE][32];

void init_zobrist() {
    for (int i = 0; i < BOARD_SIZE; i++) {
        for (int j = 0; j < 32; j++) {
            zobrist_table[i][j] = (i * 31 + j * 17 + 0xAB1234CD) ^ 0x9E3779B97F4A7C15ULL;
        }
    }
}

inline uint32_t hash_board_fast(const Board* b) {
    uint32_t hash = 0;
    for (int i = 0; i < BOARD_SIZE; i++) {
        uint8_t piece = b->squares[i];
        if (piece != EMPTY) {
            hash ^= zobrist_table[i][piece];
        }
    }
    return hash;
}

void tt_init() {
    if (shared_tt == NULL) {
        shared_tt = malloc(sizeof(TranspositionTable));
        memset(shared_tt, 0, sizeof(TranspositionTable));
    }
}

inline void tt_store(uint32_t key, int eval, int depth, int flag) {
    uint32_t idx = key & (TT_SIZE - 1);
    LockFreeTTEntry* entry = &shared_tt->entries[idx];
    
    TTEntry new_entry;
    new_entry.key = key;
    new_entry.eval = eval;
    new_entry.depth = depth;
    new_entry.flag = flag;
    
    uint64_t new_val = *(uint64_t*)&new_entry;
    atomic_store_explicit(&entry->data, new_val, memory_order_release);
}

inline bool tt_lookup(uint32_t key, int depth, int* eval, int* flag) {
    uint32_t idx = key & (TT_SIZE - 1);
    LockFreeTTEntry* entry = &shared_tt->entries[idx];
    
    uint64_t val = atomic_load_explicit(&entry->data, memory_order_acquire);
    TTEntry* stored = (TTEntry*)&val;
    
    if (stored->key == key && stored->depth >= depth) {
        *eval = stored->eval;
        *flag = stored->flag;
        return true;
    }
    return false;
}

inline void tt_clear() {
    memset(shared_tt->entries, 0, sizeof(shared_tt->entries));
}

inline bool is_valid(int r, int c) {
    return r >= 0 && r < 8 && c >= 0 && c < 8;
}

inline int rc_to_idx(int r, int c) {
    return r * 8 + c;
}

inline void idx_to_rc(int idx, int* r, int* c) {
    *r = idx / 8;
    *c = idx % 8;
}

inline uint8_t get_piece(const Board* b, int idx) {
    return b->squares[idx];
}

inline void set_piece(Board* b, int idx, uint8_t piece) {
    b->squares[idx] = piece;
}

void init_board(Board* b) {
    memset(b->squares, EMPTY, BOARD_SIZE);
    
    for (int i = 0; i < 8; i++) {
        b->squares[rc_to_idx(1, i)] = BLACK * 8 + P;
        b->squares[rc_to_idx(6, i)] = WHITE * 8 + P;
    }
    
    uint8_t back_ranks[] = { R, N, B, Q, K, B, N, R };
    for (int i = 0; i < 8; i++) {
        b->squares[rc_to_idx(0, i)] = BLACK * 8 + back_ranks[i];
        b->squares[rc_to_idx(7, i)] = WHITE * 8 + back_ranks[i];
    }
}

void print_board(const Board* b) {
    printf("      a   b   c   d   e   f   g   h\n");
    printf("    +---+---+---+---+---+---+---+---+\n");
    for (int r = 0; r < 8; r++) {
        printf(" %d  |", 8 - r);
        for (int c = 0; c < 8; c++) {
            uint8_t piece = get_piece(b, rc_to_idx(r, c));
            if (piece == EMPTY) {
                printf("   |");
            } else {
                uint8_t color = piece / 8;
                uint8_t type = piece % 8;
                char ch = "PNBRQK"[type - 1];
                if (color == BLACK) ch = tolower(ch);
                printf(" %c |", ch);
            }
        }
        printf(" %d\n", 8 - r);
        if (r < 7) printf("    +---+---+---+---+---+---+---+---+\n");
    }
    printf("    +---+---+---+---+---+---+---+---+\n");
    printf("      a   b   c   d   e   f   g   h\n\n");
}

void generate_moves_captures_first(const Board* b, uint8_t color, Move* moves, int* count) {
    *count = 0;
    Move all[MAX_MOVES];
    int all_count = 0;
    
    for (int idx = 0; idx < 64; idx++) {
        uint8_t piece = get_piece(b, idx);
        if (piece == EMPTY || piece / 8 != color) continue;
        
        uint8_t type = piece % 8;
        int r, c;
        idx_to_rc(idx, &r, &c);
        
        if (type == P) {
            int step = (color == WHITE) ? -1 : 1;
            int start_row = (color == WHITE) ? 6 : 1;
            
            int f1 = rc_to_idx(r + step, c);
            if (is_valid(r + step, c) && get_piece(b, f1) == EMPTY) {
                all[all_count].from = idx;
                all[all_count].to = f1;
                all[all_count].captured = EMPTY;
                all[all_count].flags = 0;
                all_count++;
                
                if (r == start_row) {
                    int f2 = rc_to_idx(r + 2 * step, c);
                    if (get_piece(b, f2) == EMPTY) {
                        all[all_count].from = idx;
                        all[all_count].to = f2;
                        all[all_count].captured = EMPTY;
                        all[all_count].flags = 0;
                        all_count++;
                    }
                }
            }
            
            for (int dc = -1; dc <= 1; dc += 2) {
                int nr = r + step, nc = c + dc;
                if (is_valid(nr, nc)) {
                    int t = rc_to_idx(nr, nc);
                    uint8_t target = get_piece(b, t);
                    if (target != EMPTY && target / 8 != color) {
                        all[all_count].from = idx;
                        all[all_count].to = t;
                        all[all_count].captured = target;
                        all[all_count].flags = 1;
                        all_count++;
                    }
                }
            }
        } 
        else if (type == N) {
            int knight_offs[][2] = {{2,1},{1,2},{-1,2},{-2,1},{-2,-1},{-1,-2},{1,-2},{2,-1}};
            for(int i=0; i<8; i++) {
                int nr = r + knight_offs[i][0];
                int nc = c + knight_offs[i][1];
                if(is_valid(nr, nc)) {
                    int t = rc_to_idx(nr, nc);
                    uint8_t target = get_piece(b, t);
                    if(target == EMPTY || target / 8 != color) {
                        all[all_count].from = idx;
                        all[all_count].to = t;
                        all[all_count].captured = target;
                        all[all_count].flags = (target != EMPTY) ? 1 : 0;
                        all_count++;
                    }
                }
            }
        }
        else if (type == K) {
            int king_offs[][2] = {{1,0},{-1,0},{0,1},{0,-1},{1,1},{1,-1},{-1,1},{-1,-1}};
            for(int i=0; i<8; i++) {
                int nr = r + king_offs[i][0];
                int nc = c + king_offs[i][1];
                if(is_valid(nr, nc)) {
                    int t = rc_to_idx(nr, nc);
                    uint8_t target = get_piece(b, t);
                    if(target == EMPTY || target / 8 != color) {
                        all[all_count].from = idx;
                        all[all_count].to = t;
                        all[all_count].captured = target;
                        all[all_count].flags = (target != EMPTY) ? 1 : 0;
                        all_count++;
                    }
                }
            }
        }
        else {
            int dirs[][2] = {{1,0},{-1,0},{0,1},{0,-1},{1,1},{1,-1},{-1,1},{-1,-1}};
            int max_dir = (type == R) ? 4 : (type == B) ? 4 : 8;
            
            for(int d = 0; d < max_dir; d++) {
                if (type == R && d >= 4) break;
                if (type == B && d < 4) continue;
                
                int nr = r + dirs[d][0];
                int nc = c + dirs[d][1];
                
                while(is_valid(nr, nc)) {
                    int t = rc_to_idx(nr, nc);
                    uint8_t target = get_piece(b, t);
                    
                    if (target == EMPTY) {
                        all[all_count].from = idx;
                        all[all_count].to = t;
                        all[all_count].captured = EMPTY;
                        all[all_count].flags = 0;
                        all_count++;
                    } else {
                        if (target / 8 != color) {
                            all[all_count].from = idx;
                            all[all_count].to = t;
                            all[all_count].captured = target;
                            all[all_count].flags = 1;
                            all_count++;
                        }
                        break;
                    }
                    
                    nr += dirs[d][0];
                    nc += dirs[d][1];
                }
            }
        }
    }
    
    int cap_count = 0;
    for (int i = 0; i < all_count; i++) {
        if (all[i].captured != EMPTY) {
            moves[cap_count++] = all[i];
        }
    }
    for (int i = 0; i < all_count; i++) {
        if (all[i].captured == EMPTY) {
            moves[cap_count++] = all[i];
        }
    }
    
    *count = all_count;
}

inline bool is_attacked(const Board* b, int idx, uint8_t attacker_color) {
    int r, c;
    idx_to_rc(idx, &r, &c);
    
    int pawn_step = (attacker_color == WHITE) ? 1 : -1;
    for (int dc = -1; dc <= 1; dc += 2) {
        int nr = r + pawn_step, nc = c + dc;
        if (is_valid(nr, nc)) {
            uint8_t p = get_piece(b, rc_to_idx(nr, nc));
            if (p == attacker_color * 8 + P) return true;
        }
    }
    
    int knight_offs[][2] = {{2,1},{1,2},{-1,2},{-2,1},{-2,-1},{-1,-2},{1,-2},{2,-1}};
    for(int i=0; i<8; i++) {
        int nr = r + knight_offs[i][0];
        int nc = c + knight_offs[i][1];
        if(is_valid(nr, nc)) {
            uint8_t p = get_piece(b, rc_to_idx(nr, nc));
            if (p == attacker_color * 8 + N) return true;
        }
    }
    
    for(int dr = -1; dr <= 1; dr++) {
        for(int dc = -1; dc <= 1; dc++) {
            if (dr == 0 && dc == 0) continue;
            int nr = r + dr, nc = c + dc;
            if(is_valid(nr, nc)) {
                uint8_t p = get_piece(b, rc_to_idx(nr, nc));
                if (p == attacker_color * 8 + K) return true;
            }
        }
    }
    
    int dirs[][2] = {{1,0},{-1,0},{0,1},{0,-1},{1,1},{1,-1},{-1,1},{-1,-1}};
    for(int i=0; i<8; i++) {
        int nr = r + dirs[i][0];
        int nc = c + dirs[i][1];
        bool is_orth = (i < 4);
        
        while(is_valid(nr, nc)) {
            uint8_t p = get_piece(b, rc_to_idx(nr, nc));
            if (p != EMPTY) {
                if (p / 8 == attacker_color) {
                    uint8_t type = p % 8;
                    if (type == Q) return true;
                    if (is_orth && type == R) return true;
                    if (!is_orth && type == B) return true;
                }
                break;
            }
            nr += dirs[i][0];
            nc += dirs[i][1];
        }
    }
    
    return false;
}

inline bool in_check(const Board* b, uint8_t color) {
    uint8_t king = color * 8 + K;
    for (int i = 0; i < 64; i++) {
        if (get_piece(b, i) == king) {
            uint8_t enemy = (color == WHITE) ? BLACK : WHITE;
            return is_attacked(b, i, enemy);
        }
    }
    return true;
}

inline void make_move(Board* b, Move* m) {
    m->captured = get_piece(b, m->to);
    set_piece(b, m->to, get_piece(b, m->from));
    set_piece(b, m->from, EMPTY);
}

inline void undo_move(Board* b, Move* m) {
    set_piece(b, m->from, get_piece(b, m->to));
    set_piece(b, m->to, m->captured);
}

inline bool is_legal(Board* b, Move* m, uint8_t color) {
    make_move(b, m);
    bool check = in_check(b, color);
    undo_move(b, m);
    return !check;
}

const int8_t pst_pawn_mg[64] = {
     0,   0,   0,   0,   0,   0,   0,   0,
    50,  50,  50,  50,  50,  50,  50,  50,
    10,  10,  20,  30,  30,  20,  10,  10,
     5,   5,  10,  25,  25,  10,   5,   5,
     0,   0,   0,  20,  20,   0,   0,   0,
     5,  -5, -10,   0,   0, -10,  -5,   5,
     5,  10,  10, -20, -20,  10,  10,   5,
     0,   0,   0,   0,   0,   0,   0,   0
};

const int8_t pst_pawn_eg[64] = {
     0,   0,   0,   0,   0,   0,   0,   0,
   178, 173, 100,  94,  94, 100, 173, 178,
    94, 100,  85,  67,  67,  85, 100,  94,
    67,  75,  70,  50,  50,  70,  75,  67,
    50,  50,  45,  40,  40,  45,  50,  50,
    45,  40,  35,  30,  30,  35,  40,  45,
    40,  35,  30,  25,  25,  30,  35,  40,
     0,   0,   0,   0,   0,   0,   0,   0
};

const int8_t pst_knight_mg[64] = {
    -50, -40, -30, -30, -30, -30, -40, -50,
    -40, -20,   0,   5,   5,   0, -20, -40,
    -30,   5,  10,  15,  15,  10,   5, -30,
    -30,   0,  15,  20,  20,  15,   0, -30,
    -30,   5,  15,  20,  20,  15,   5, -30,
    -30,   0,  10,  15,  15,  10,   0, -30,
    -40, -20,   0,   0,   0,   0, -20, -40,
    -50, -40, -30, -30, -30, -30, -40, -50
};

const int8_t pst_knight_eg[64] = {
    -50, -40, -30, -30, -30, -30, -40, -50,
    -40, -20,   0,   5,   5,   0, -20, -40,
    -30,   5,  10,  15,  15,  10,   5, -30,
    -30,   0,  15,  20,  20,  15,   0, -30,
    -30,   5,  15,  20,  20,  15,   5, -30,
    -30,   0,  10,  15,  15,  10,   0, -30,
    -40, -20,   0,   0,   0,   0, -20, -40,
    -50, -40, -30, -30, -30, -30, -40, -50
};

const int8_t pst_bishop_mg[64] = {
    -20, -10, -10, -10, -10, -10, -10, -20,
    -10,   5,   0,   0,   0,   0,   5, -10,
    -10,  10,  10,  10,  10,  10,  10, -10,
    -10,   0,  10,  15,  15,  10,   0, -10,
    -10,   5,  10,  15,  15,  10,   5, -10,
    -10,   0,   5,  10,  10,   5,   0, -10,
    -10,   0,   0,   0,   0,   0,   0, -10,
    -20, -10, -10, -10, -10, -10, -10, -20
};

const int8_t pst_bishop_eg[64] = {
    -20, -10, -10, -10, -10, -10, -10, -20,
    -10,   5,   0,   0,   0,   0,   5, -10,
    -10,  10,  10,  10,  10,  10,  10, -10,
    -10,   0,  10,  15,  15,  10,   0, -10,
    -10,   5,  10,  15,  15,  10,   5, -10,
    -10,   0,   5,  10,  10,   5,   0, -10,
    -10,   0,   0,   0,   0,   0,   0, -10,
    -20, -10, -10, -10, -10, -10, -10, -20
};

const int8_t pst_rook_mg[64] = {
      0,   0,   0,   5,   5,   0,   0,   0,
     -5,   0,   0,   0,   0,   0,   0,  -5,
     -5,   0,   0,   0,   0,   0,   0,  -5,
     -5,   0,   0,   0,   0,   0,   0,  -5,
     -5,   0,   0,   0,   0,   0,   0,  -5,
     -5,   0,   0,   0,   0,   0,   0,  -5,
      5,  10,  10,  10,  10,  10,  10,   5,
      0,   0,   0,   0,   0,   0,   0,   0
};

const int8_t pst_rook_eg[64] = {
      0,   0,   0,   5,   5,   0,   0,   0,
     -5,   0,   0,   0,   0,   0,   0,  -5,
     -5,   0,   0,   0,   0,   0,   0,  -5,
     -5,   0,   0,   0,   0,   0,   0,  -5,
     -5,   0,   0,   0,   0,   0,   0,  -5,
     -5,   0,   0,   0,   0,   0,   0,  -5,
      5,  10,  10,  10,  10,  10,  10,   5,
      0,   0,   0,   0,   0,   0,   0,   0
};

const int8_t pst_queen_mg[64] = {
    -20, -10, -10,  -5,  -5, -10, -10, -20,
    -10,   0,   5,   0,   0,   0,   0, -10,
    -10,   5,   5,   5,   5,   5,   0, -10,
      0,   0,   5,   5,   5,   5,   0,  -5,
     -5,   0,   5,   5,   5,   5,   0,  -5,
    -10,   0,   5,   5,   5,   5,   0, -10,
    -10,   0,   0,   0,   0,   0,   0, -10,
    -20, -10, -10,  -5,  -5, -10, -10, -20
};

const int8_t pst_queen_eg[64] = {
    -20, -10, -10,  -5,  -5, -10, -10, -20,
    -10,   0,   5,   0,   0,   0,   0, -10,
    -10,   5,   5,   5,   5,   5,   0, -10,
      0,   0,   5,   5,   5,   5,   0,  -5,
     -5,   0,   5,   5,   5,   5,   0,  -5,
    -10,   0,   5,   5,   5,   5,   0, -10,
    -10,   0,   0,   0,   0,   0,   0, -10,
    -20, -10, -10,  -5,  -5, -10, -10, -20
};

const int8_t pst_king_mg[64] = {
    -30, -40, -40, -50, -50, -40, -40, -30,
    -30, -40, -40, -50, -50, -40, -40, -30,
    -30, -40, -40, -50, -50, -40, -40, -30,
    -30, -40, -40, -50, -50, -40, -40, -30,
    -20, -30, -30, -40, -40, -30, -30, -20,
    -10, -20, -20, -20, -20, -20, -20, -10,
     20,  20,   0,   0,   0,   0,  20,  20,
     20,  30,  10,   0,   0,  10,  30,  20
};

const int8_t pst_king_eg[64] = {
    -50, -40, -30, -20, -20, -30, -40, -50,
    -30, -20, -10,   0,   0, -10, -20, -30,
    -20, -10,  10,  20,  20,  10, -10, -20,
    -10,   0,  20,  30,  30,  20,   0, -10,
    -10,   0,  20,  30,  30,  20,   0, -10,
    -20, -10,  10,  20,  20,  10, -10, -20,
    -30, -20, -10,   0,   0, -10, -20, -30,
    -50, -40, -30, -20, -20, -30, -40, -50
};

bool is_endgame(const Board* b) {
    int material = 0;
    for (int i = 0; i < 64; i++) {
        uint8_t piece = get_piece(b, i);
        if (piece == EMPTY) continue;
        uint8_t type = piece % 8;
        if (type == N) material += 3;
        else if (type == B) material += 3;
        else if (type == R) material += 5;
        else if (type == Q) material += 9;
    }
    return material < 15;
}

int evaluate_fast(const Board* b) {
    int score = 0;
    bool eg = is_endgame(b);
    int bk_idx = -1, wk_idx = -1;
    int black_pawns = 0, white_pawns = 0;
    
    for (int i = 0; i < 64; i++) {
        uint8_t piece = get_piece(b, i);
        if (piece == EMPTY) continue;
        
        uint8_t color = piece / 8;
        uint8_t type = piece % 8;
        int material_value = 0;
        int pst_value = 0;
        
        switch(type) {
            case P: 
                material_value = 100;
                pst_value = eg ? pst_pawn_eg[i] : pst_pawn_mg[i];
                if (color == BLACK) black_pawns++;
                else white_pawns++;
                break;
            case N: 
                material_value = 320;
                pst_value = eg ? pst_knight_eg[i] : pst_knight_mg[i];
                break;
            case B: 
                material_value = 330;
                pst_value = eg ? pst_bishop_eg[i] : pst_bishop_mg[i];
                break;
            case R: 
                material_value = 500;
                pst_value = eg ? pst_rook_eg[i] : pst_rook_mg[i];
                if ((color == BLACK && i / 8 == 6) || (color == WHITE && i / 8 == 1)) {
                    pst_value += 50;
                }
                break;
            case Q: 
                material_value = 900;
                pst_value = eg ? pst_queen_eg[i] : pst_queen_mg[i];
                break;
            case K: 
                material_value = 0;
                pst_value = eg ? pst_king_eg[i] : pst_king_mg[i];
                if (color == BLACK) bk_idx = i;
                else wk_idx = i;
                break;
        }
        
        if (color == BLACK) {
            score += material_value + (pst_value / 4);
        } else {
            score -= material_value + (pst_value / 4);
        }
    }
    
    for (int c = 0; c < 8; c++) {
        int black_col = 0, white_col = 0;
        for (int r = 0; r < 8; r++) {
            uint8_t piece = get_piece(b, rc_to_idx(r, c));
            if (piece == BLACK * 8 + P) black_col++;
            if (piece == WHITE * 8 + P) white_col++;
        }
        if (black_col > 1) score += (black_col - 1) * 25;
        if (white_col > 1) score -= (white_col - 1) * 25;
    }
    
    for (int i = 0; i < 64; i++) {
        uint8_t piece = get_piece(b, i);
        if (piece != BLACK * 8 + P && piece != WHITE * 8 + P) continue;
        
        int col = i % 8;
        bool isolated = true;
        
        if (col > 0) {
            for (int r = 0; r < 8; r++) {
                uint8_t p = get_piece(b, rc_to_idx(r, col - 1));
                if ((piece == BLACK * 8 + P && p == BLACK * 8 + P) ||
                    (piece == WHITE * 8 + P && p == WHITE * 8 + P)) {
                    isolated = false;
                    break;
                }
            }
        }
        if (isolated && col < 7) {
            for (int r = 0; r < 8; r++) {
                uint8_t p = get_piece(b, rc_to_idx(r, col + 1));
                if ((piece == BLACK * 8 + P && p == BLACK * 8 + P) ||
                    (piece == WHITE * 8 + P && p == WHITE * 8 + P)) {
                    isolated = false;
                    break;
                }
            }
        }
        
        if (isolated) {
            if (piece == BLACK * 8 + P) score += 15;
            else score -= 15;
        }
    }
    
    if (!eg) {
        if (bk_idx != -1) {
            int r = bk_idx / 8, c = bk_idx % 8;
            if (r > 1 && r < 6 && c > 1 && c < 6) {
                score += 40;  
            }
        }
        if (wk_idx != -1) {
            int r = wk_idx / 8, c = wk_idx % 8;
            if (r > 1 && r < 6 && c > 1 && c < 6) {
                score -= 40;  
            }
        }
    } else {
        if (bk_idx != -1) {
            int r = bk_idx / 8, c = bk_idx % 8;
            int dist_to_center = abs(r - 4) + abs(c - 4);
            score -= dist_to_center * 5;  
        }
        if (wk_idx != -1) {
            int r = wk_idx / 8, c = wk_idx % 8;
            int dist_to_center = abs(r - 4) + abs(c - 4);
            score += dist_to_center * 5;  
        }
    }
    
    int center_squares[] = {27, 28, 35, 36};  
    for (int i = 0; i < 4; i++) {
        int sq = center_squares[i];
        uint8_t piece = get_piece(b, sq);
        if (piece != EMPTY) {
            uint8_t type = piece % 8;
            uint8_t color = piece / 8;
            int bonus = 0;
            
            if (type == P) bonus = 15;
            else if (type == N) bonus = 10;
            else if (type == B) bonus = 8;
            else if (type == R) bonus = 5;
            else if (type == Q) bonus = 10;
            
            if (color == BLACK) score += bonus;
            else score -= bonus;
        }
    }
    
    for (int i = 0; i < 64; i++) {
        uint8_t piece = get_piece(b, i);
        if (piece != BLACK * 8 + P && piece != WHITE * 8 + P) continue;
        
        int col = i % 8;
        int row = i / 8;
        bool passed = true;
        
        if (piece == BLACK * 8 + P) {
            for (int r = row + 1; r < 8; r++) {
                for (int c = col - 1; c <= col + 1; c++) {
                    if (c >= 0 && c < 8) {
                        uint8_t p = get_piece(b, rc_to_idx(r, c));
                        if (p == WHITE * 8 + P) {
                            passed = false;
                            break;
                        }
                    }
                }
                if (!passed) break;
            }
            if (passed) score += (7 - row) * 20;  
        } else {
            for (int r = row - 1; r >= 0; r--) {
                for (int c = col - 1; c <= col + 1; c++) {
                    if (c >= 0 && c < 8) {
                        uint8_t p = get_piece(b, rc_to_idx(r, c));
                        if (p == BLACK * 8 + P) {
                            passed = false;
                            break;
                        }
                    }
                }
                if (!passed) break;
            }
            if (passed) score -= (row) * 20;  
        }
    }
    
    int black_bishops = 0, white_bishops = 0;
    for (int i = 0; i < 64; i++) {
        uint8_t piece = get_piece(b, i);
        if (piece == BLACK * 8 + B) black_bishops++;
        if (piece == WHITE * 8 + B) white_bishops++;
    }
    if (black_bishops >= 2) score += 30;
    if (white_bishops >= 2) score -= 30;
    
    
    return score;
}

inline void add_killer(int depth, int move) {
    if (move != killer_moves[depth][0]) {
        killer_moves[depth][1] = killer_moves[depth][0];
        killer_moves[depth][0] = move;
    }
}

int pvs(Board* b, int depth, int alpha, int beta, bool maximizing, int ply) {
    if (debug_pvs) printf("PVS Entry: Depth=%d, Ply=%d, Key=%u\n", depth, ply, hash_board_fast(b));
    uint32_t key = hash_board_fast(b);
    int cached_eval, cached_flag;
    if (tt_lookup(key, depth, &cached_eval, &cached_flag)) {
        if (cached_flag == 0) return cached_eval;
        if (cached_flag == 1) alpha = (alpha > cached_eval) ? alpha : cached_eval;
        if (cached_flag == 2) beta = (beta < cached_eval) ? beta : cached_eval;
        if (alpha >= beta) return cached_eval;
    }
    
    if (depth <= 0) {
        int eval = evaluate_fast(b);
        tt_store(key, eval, 0, 0);
        return eval;
    }
    
    Move moves[MAX_MOVES];
    int count;
    generate_moves_captures_first(b, maximizing ? BLACK : WHITE, moves, &count);
    
    int legal_count = 0;
    for(int i=0; i<count; i++) {
        if(is_legal(b, &moves[i], maximizing ? BLACK : WHITE)) {
            moves[legal_count++] = moves[i];
        }
    }
    
    if (legal_count == 0) {
        if (in_check(b, maximizing ? BLACK : WHITE)) {
            return -MATE_SCORE + ply;
        }
        return 0;
    }
    
    int original_alpha = alpha;
    int best_eval = -INF;
    int result_flag;
    
    if (maximizing) {
        for (int i = 0; i < legal_count; i++) {
            int new_depth = depth - 1;
            if (ply >= 3 && i > 3 && moves[i].captured == EMPTY && depth > 2) {
                new_depth = depth - 2;
            }
            
            make_move(b, &moves[i]);
            int eval = pvs(b, new_depth, alpha, beta, false, ply + 1);
            undo_move(b, &moves[i]);
            
            if (eval > best_eval) best_eval = eval;
            if (eval > alpha) alpha = eval;
            if (beta <= alpha) {
                add_killer(ply, moves[i].from | (moves[i].to << 8));
                break;
            }
        }
    } else {
        for (int i = 0; i < legal_count; i++) {
            int new_depth = depth - 1;
            if (ply >= 3 && i > 3 && moves[i].captured == EMPTY && depth > 2) {
                new_depth = depth - 2;
            }
            
            make_move(b, &moves[i]);
            int eval = pvs(b, new_depth, alpha, beta, true, ply + 1);
            undo_move(b, &moves[i]);
            
            if (eval < best_eval) best_eval = eval;
            if (eval < beta) beta = eval;
            if (beta <= alpha) {
                add_killer(ply, moves[i].from | (moves[i].to << 8));
                break;
            }
        }
    }
    
    result_flag = (best_eval <= original_alpha) ? 2 : (best_eval >= beta) ? 1 : 0;
    tt_store(key, best_eval, depth, result_flag);
    return best_eval;
}

void* worker_thread(void* arg) {
    memset(killer_moves, 0, sizeof(killer_moves));
    while (1) sleep_ms(100);
    return NULL;
}

void start_thread_pool(int threads) {
    num_threads = threads;
    tt_init();
    
    for (int i = 1; i < num_threads; i++) {
        pthread_create(&thread_pool[i], NULL, worker_thread, NULL);
    }
}

int parse_input(const char* str) {
    if (strlen(str) < 2) return -1;
    int c = str[0] - 'a';
    int r = 8 - (str[1] - '0');
    if (!is_valid(r, c)) return -1;
    return rc_to_idx(r, c);
}

void idx_to_alg(int idx, char* out) {
    int r, c;
    idx_to_rc(idx, &r, &c);
    out[0] = 'a' + c;
    out[1] = '0' + (8 - r);
    out[2] = '\0';
}

void player_move(Board* b) {
    char buf[16];
    while (true) {
        printf("Player 1 move (format: e2 e4): ");
        if (scanf("%15s", buf) != 1) continue;
        int from = parse_input(buf);
        if (scanf("%15s", buf) != 1) continue;
        int to = parse_input(buf);
        
        if (from == -1 || to == -1) {
            printf("Invalid squares.\n");
            continue;
        }
        
        Move all_moves[MAX_MOVES];
        int count = 0;
        generate_moves_captures_first(b, WHITE, all_moves, &count);
        
        bool found = false;
        for(int i=0; i<count; i++) {
            if(all_moves[i].from == from && all_moves[i].to == to) {
                if(is_legal(b, &all_moves[i], WHITE)) {
                    make_move(b, &all_moves[i]);
                    found = true;
                    break;
                }
            }
        }
        
        if (!found) printf("Illegal move. Try again.\n");
        else break;
    }
}

void computer_move(Board* b, int difficulty, int depth) {
    Move moves[MAX_MOVES];
    int count;
    generate_moves_captures_first(b, BLACK, moves, &count);
    
    int legal_count = 0;
    Move legal_moves[MAX_MOVES];
    for(int i=0; i<count; i++) {
        if(is_legal(b, &moves[i], BLACK)) {
            legal_moves[legal_count++] = moves[i];
        }
    }
    
    if (legal_count == 0) return;
    
    Move chosen = legal_moves[0];
    
    if (difficulty == 1) {
        chosen = legal_moves[rand() % legal_count];
    } else if (difficulty == 2) {
        bool found = false;
        for(int i=0; i<legal_count; i++) {
            if(legal_moves[i].captured != EMPTY) {
                chosen = legal_moves[i];
                found = true;
                break;
            }
        }
        if(!found) chosen = legal_moves[rand() % legal_count];
    } else {
        tt_clear();
        int best_eval = -INF;
        for(int i=0; i<legal_count; i++) {
            make_move(b, &legal_moves[i]);
            int eval = pvs(b, depth, -INF, INF, false, 0);
            undo_move(b, &legal_moves[i]);
            
            if(eval > best_eval) {
                best_eval = eval;
                chosen = legal_moves[i];
            }
        }
    }
    
    char from_alg[3], to_alg[3];
    idx_to_alg(chosen.from, from_alg);
    idx_to_alg(chosen.to, to_alg);
    printf("Computer moves %s -> %s\n", from_alg, to_alg);
    make_move(b, &chosen);
}

int select_thread_count() {
    int cpu_count = get_cpu_count();
    char buf[32];
    
    printf("CPU cores detected: %d\n", cpu_count);
    printf("Enter number of threads (default=%d, max=%d): ", cpu_count, MAX_THREADS);
    
    if (scanf("%31s", buf) != 1) {
        return cpu_count;
    }
    
    char* endptr;
    int threads = (int)strtol(buf, &endptr, 10);
    
    if (endptr == buf || *endptr != '\0' || threads < 1) {
        return cpu_count;
    }
    
    if (threads > cpu_count) {
        printf("Capping at CPU count: %d threads\n", cpu_count);
        return cpu_count;
    }
    
    if (threads > MAX_THREADS) {
        printf("Capping at max: %d threads\n", MAX_THREADS);
        return MAX_THREADS;
    }
    
    return threads;
}

int select_difficulty() {
    char buf[32];
    while (true) {
        printf("Select difficulty (1=Beginner, 2=Easy, 3=Hard): ");
        (void)scanf("%31s", buf);
        if (strcmp(buf, "1") == 0 || strcmp(buf, "Beginner") == 0) return 1;
        if (strcmp(buf, "2") == 0 || strcmp(buf, "Easy") == 0) return 2;
        if (strcmp(buf, "3") == 0 || strcmp(buf, "Hard") == 0) return 3;
        printf("Invalid choice.\n");
    }
}

int select_search_depth() {
    char buf[32];
    printf("\n=== Hard Mode Configuration ===\n");
    printf("Enter search depth (default=8): ");
    
    if (scanf("%31s", buf) != 1) {
        printf("Using depth 8.\n\n");
        return 8;
    }
    
    char* endptr;
    int depth = (int)strtol(buf, &endptr, 10);
    
    if (endptr == buf || *endptr != '\0' || depth < 1) {
        printf("Using depth 8.\n\n");
        return 8;
    }
    
    printf("Using depth %d.\n\n", depth);
    return depth;
}


int select_debug() {
    char buf[4];
    printf("Enter debug (1=true, 0=false, default=false): ");
    
    if (scanf("%3s", buf) != 1) {
        printf("Input error. Not debugging.\n\n");
        return 0;
    }
    
    char* endptr;
    long val = strtol(buf, &endptr, 10);
    
    if (endptr == buf || *endptr != '\0') {
        printf("Invalid input. Not debugging.\n\n");
        return 0;
    }

    bool debug = (val != 0);
    
    if (debug) {
        printf("Using debug value: %d.\n\n", (int)debug);
        return 1;
    } else {
        printf("Not debugging.\n\n");
        return 0;
    }
}

void check_game_over(Board* b, uint8_t turn) {
    Move moves[MAX_MOVES];
    int count;
    generate_moves_captures_first(b, turn, moves, &count);
    
    int legal = 0;
    for(int i=0; i<count; i++) if(is_legal(b, &moves[i], turn)) legal++;
    
    if (legal == 0) {
        if (in_check(b, turn)) printf("Checkmate!\n");
        else printf("Stalemate!\n");
        exit(0);
    }
}

void output_board_raw(const Board* b, const char* filename) {
    FILE* f = fopen(filename, "w");
    if (!f) {
        fprintf(stderr, "Error: Cannot write to %s\n", filename);
        return;
    }
    
    fprintf(f, "      A   B   C   D   E   F   G   H\n");
    fprintf(f, "    +---+---+---+---+---+---+---+---+\n");
    
    for (int r = 0; r < 8; r++) {
        fprintf(f, " %d  |", 8 - r);
        for (int c = 0; c < 8; c++) {
            uint8_t piece = get_piece(b, rc_to_idx(r, c));
            if (piece == EMPTY) {
                fprintf(f, "   |");
            } else {
                uint8_t color = piece / 8;
                uint8_t type = piece % 8;
                char ch = "PNBRQK"[type - 1];
                if (color == BLACK) ch = tolower(ch);
                fprintf(f, " %c |", ch);
            }
        }
        fprintf(f, " %d\n", 8 - r);
        
        if (r < 7) {
            fprintf(f, "    +---+---+---+---+---+---+---+---+\n");
        }
    }
    
    fprintf(f, "    +---+---+---+---+---+---+---+---+\n");
    fprintf(f, "      A   B   C   D   E   F   G   H\n");
    
    fclose(f);
}

void load_board_raw(Board* b, const char* data_str) {
    memset(b->squares, EMPTY, BOARD_SIZE);
    
    
    char buffer[16384];
    strncpy(buffer, data_str, sizeof(buffer) - 1);
    buffer[sizeof(buffer) - 1] = '\0';
    
    int row = 0;
    char* line = strtok(buffer, "\n");
    
    while (line && row < 8) {
        if (strchr(line, 'A') || strchr(line, '+') || strlen(line) < 5) {
            line = strtok(NULL, "\n");
            continue;
        }
        
        int col = 0;
        for (int i = 0; line[i] && col < 8; i++) {
            if (line[i] == '|') {
                int j = i + 1;
                while (j < (int)strlen(line) && line[j] == ' ') j++;
                
                if (j < (int)strlen(line) && line[j] != '|') {
                    char piece_ch = line[j];
                    uint8_t piece = EMPTY;
                    
                    if (piece_ch != ' ') {
                        uint8_t color = isupper(piece_ch) ? WHITE : BLACK;
                        char upper_ch = toupper(piece_ch);
                        
                        switch (upper_ch) {
                            case 'P': piece = color * 8 + P; break;
                            case 'N': piece = color * 8 + N; break;
                            case 'B': piece = color * 8 + B; break;
                            case 'R': piece = color * 8 + R; break;
                            case 'Q': piece = color * 8 + Q; break;
                            case 'K': piece = color * 8 + K; break;
                        }
                    }
                    
                    set_piece(b, rc_to_idx(row, col), piece);
                    col++;
                }
            }
        }
        
        if (col == 8) row++;  
        line = strtok(NULL, "\n");
    }
}

void parse_cli_args(int argc, char* argv[], char** input_file, char** output_file, 
                    char** move_from, char** move_to, int* debug, int* threads, 
                    int* difficulty, int* depth) {
    for (int i = 1; i < argc; i++) {
        char* arg = argv[i];
        char* value = strchr(arg, '=');
        
        if (!value) continue;
        *value = '\0';
        value++;
        
        if (strcmp(arg, "-i") == 0) {
            *input_file = value;
        } else if (strcmp(arg, "-o") == 0) {
            *output_file = value;
        } else if (strcmp(arg, "-m") == 0) {
            *move_from = value;
            for (int j = i + 1; j < argc; j++) {
                if (argv[j][0] != '-') {
                    *move_to = argv[j];
                    i = j;
                    break;
                }
            }
        } else if (strcmp(arg, "-d") == 0) {
            *debug = atoi(value);
        } else if (strcmp(arg, "-t") == 0 || strcmp(arg, "-threads") == 0) {
            *threads = atoi(value);
        } else if (strcmp(arg, "-diff") == 0 || strcmp(arg, "-difficulty") == 0) {
            *difficulty = atoi(value);
        } else if (strcmp(arg, "-depth") == 0) {
            *depth = atoi(value);
        }
    }
}

bool apply_move_from_alg(Board* b, const char* from_alg, const char* to_alg) {
    int from = parse_input(from_alg);
    int to = parse_input(to_alg);
    
    if (from == -1 || to == -1) {
        fprintf(stderr, "Invalid squares: %s -> %s\n", from_alg, to_alg);
        return false;
    }
    
    uint8_t source_piece = get_piece(b, from);
    if (source_piece == EMPTY) {
        fprintf(stderr, "No piece at source square: %s\n", from_alg);
        return false;
    }
    
    uint8_t moving_color = source_piece / 8;
    
    Move all_moves[MAX_MOVES];
    int count = 0;
    generate_moves_captures_first(b, moving_color, all_moves, &count);
    
    for (int i = 0; i < count; i++) {
        if (all_moves[i].from == from && all_moves[i].to == to) {
            if (is_legal(b, &all_moves[i], moving_color)) {
                make_move(b, &all_moves[i]);
                return true;
            }
        }
    }
    
    fprintf(stderr, "Illegal move: %s -> %s\n", from_alg, to_alg);
    return false;
}

void get_default_board(Board* b) {
    init_board(b);
}

int main(int argc, char* argv[]) {
    #ifdef _WIN32
    SetConsoleOutputCP(CP_UTF8);
    #endif
    
    char* input_file = NULL;
    char* output_file = NULL;
    char* move_from = NULL;
    char* move_to = NULL;
    int cli_debug = 0;
    int cli_threads = 1;
    int cli_difficulty = 2;
    int cli_depth = 6;
    
    if (argc > 1) {
        parse_cli_args(argc, argv, &input_file, &output_file, &move_from, &move_to, 
                      &cli_debug, &cli_threads, &cli_difficulty, &cli_depth);
        
        if (!move_from || !move_to || !output_file) {
            fprintf(stderr, "Usage: chess -m=<from> <to> -o=<output_file> [-i=<input_file>] [options]\n");
            fprintf(stderr, "\nRequired:\n");
            fprintf(stderr, "  -m=FROM TO            Move in algebraic notation (e.g., e2 e4)\n");
            fprintf(stderr, "  -o=FILE               Output board file\n");
            fprintf(stderr, "\nOptional:\n");
            fprintf(stderr, "  -i=FILE               Input board file (default: standard starting position)\n");
            fprintf(stderr, "  -d=<0|1>              Debug output (default=0)\n");
            fprintf(stderr, "  -t=<threads>          Number of threads (default=1)\n");
            fprintf(stderr, "  -diff=<1|2|3>         Difficulty: 1=Beginner, 2=Easy, 3=Hard (default=2)\n");
            fprintf(stderr, "  -depth=<depth>        Search depth for Hard mode (default=6)\n");
            fprintf(stderr, "\nExamples:\n");
            fprintf(stderr, "  chess -m=e2 e4 -o=board.txt\n");
            fprintf(stderr, "  chess -i=board.txt -m=e2 e4 -o=result.txt -d=1 -t=4\n");
            return 1;
        }
        
        srand(time(NULL));
        init_zobrist();
        tt_init();
        
        Board board;
        memset(&board, 0, sizeof(Board));
        
        if (input_file) {
            FILE* f = fopen(input_file, "r");
            if (!f) {
                fprintf(stderr, "Error: Cannot read input file %s\n", input_file);
                return 1;
            }
            
            char file_buffer[8192] = {0};
            size_t bytes_read = fread(file_buffer, 1, sizeof(file_buffer) - 1, f);
            fclose(f);
            file_buffer[bytes_read] = '\0';
            
            load_board_raw(&board, file_buffer);
        } else {
            init_board(&board);
        }
        
        int thread_count = (cli_threads > 1) ? cli_threads : 1;
        if (thread_count > 1) {
            start_thread_pool(thread_count);
            if (cli_debug) printf("Started with %d threads\n", thread_count);
        }
        
        debug_pvs = cli_debug;
        
        if (cli_debug) {
            printf("Input file: %s\n", input_file);
            printf("Move: %s -> %s\n", move_from, move_to);
            printf("Output file: %s\n", output_file);
            printf("Difficulty: %d, Depth: %d\n", cli_difficulty, cli_depth);
            printf("\nBoard before move:\n");
            print_board(&board);
        }
        
        if (!apply_move_from_alg(&board, move_from, move_to)) {
            fprintf(stderr, "Failed to apply move\n");
            return 1;
        }
        
        if (cli_debug) {
            printf("Board after move:\n");
            print_board(&board);
        }
        
        output_board_raw(&board, output_file);
        
        if (cli_debug) {
            printf("Output saved to: %s\n", output_file);
        }
        
        return 0;
    }
    
    srand(time(NULL));
    init_zobrist();
    tt_init();
    
    Board board;
    init_board(&board);
    print_board(&board);
    
    int thread_count = select_thread_count();
    start_thread_pool(thread_count);
    printf("Started with %d threads, shared transposition table\n\n", thread_count);
    
    int difficulty = select_difficulty();
    int search_depth = 6;

    debug_pvs = select_debug();
    
    if (difficulty == 3) {
        search_depth = select_search_depth();
    }
    
    uint8_t turn = WHITE;
    
    printf("Chess Game Started\n");
    printf("(P=pawn, N=knight, B=bishop, R=rook, Q=queen, K=king)\n");
    printf("(Uppercase=White, Lowercase=Black)\n");
    if (difficulty == 3) {
        printf("(Computer search depth: %d)\n", search_depth);
    }
    printf("\n");
    
    while (true) {
        if (turn == WHITE) {
            player_move(&board);
        } else {
            computer_move(&board, difficulty, search_depth);
        }
        
        print_board(&board);
        check_game_over(&board, turn);
        
        turn = (turn == WHITE) ? BLACK : WHITE;
    }
    
    return 0;
}
