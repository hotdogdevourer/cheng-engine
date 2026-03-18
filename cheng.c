#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <stdint.h>
#include <time.h>
#include <math.h>
#include <ctype.h>
#include <pthread.h>

#ifdef _WIN32
#include <windows.h>
#endif

#ifdef _WIN32
#include <sysinfoapi.h>
static int get_cpu_count() {
    SYSTEM_INFO sysinfo;
    GetSystemInfo(&sysinfo);
    return sysinfo.dwNumberOfProcessors;
}
#else
#include <unistd.h>
static int get_cpu_count() {
    int count = sysconf(_SC_NPROCESSORS_ONLN);
    return count > 0 ? count : 1;
}
#endif

#define MAX_THREADS 256

#define TT_SIZE 262144  
/*
   TT_SIZE LOOKUP TABLE (STRICTLY POWER OF 2 ENTRIES)
   Formula: Entries = (Megabytes * 1024 * 1024) / 8 bytes per entry
   WARNING: Memory Usage = TT_SIZE * 8 bytes * NUMBER_OF_THREADS
            With 12 threads, 128 MB/table = 1.5 GB Total RAM.
            With 12 threads, 16 GB/table = 192 GB Total RAM (WILL CRASH MOST PCS).
   
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

#define EMPTY 0
#define WHITE 1
#define BLACK 2
#define P 1
#define N 2
#define B 3
#define R 4
#define Q 5
#define K 6

#define BOARD_SIZE 64
#define MAX_MOVES 256
#define INF 32000
#define MATE_SCORE 30000

inline void tt_init();
inline void tt_store(uint32_t key, int eval, int depth, int flag);
inline bool tt_lookup(uint32_t key, int depth, int* eval, int* flag);
inline void tt_clear();

const int8_t pst_pawn[64] = {
     0,  0,  0,  0,  0,  0,  0,  0,
    50, 50, 50, 50, 50, 50, 50, 50,
    10, 10, 20, 30, 30, 20, 10, 10,
     5,  5, 10, 25, 25, 10,  5,  5,
     0,  0,  0, 20, 20,  0,  0,  0,
     5, -5,-10,  0,  0,-10, -5,  5,
     5, 10, 10,-20,-20, 10, 10,  5,
     0,  0,  0,  0,  0,  0,  0,  0
};

const int8_t pst_knight[64] = {
    -50,-40,-30,-30,-30,-30,-40,-50,
    -40,-20,  0,  0,  0,  0,-20,-40,
    -30,  0, 10, 15, 15, 10,  0,-30,
    -30,  5, 15, 20, 20, 15,  5,-30,
    -30,  0, 15, 20, 20, 15,  0,-30,
    -30,  5, 10, 15, 15, 10,  5,-30,
    -40,-20,  0,  5,  5,  0,-20,-40,
    -50,-40,-30,-30,-30,-30,-40,-50
};

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
    uint16_t depth;     
} TTEntry;

typedef struct {
    TTEntry entries[TT_SIZE];
} TranspositionTable;

__thread TranspositionTable* thread_local_tt = NULL;

int num_threads = 1;

void init_thread_local_tt() {
    if (thread_local_tt == NULL) {
        thread_local_tt = malloc(sizeof(TranspositionTable));
        memset(thread_local_tt, 0, sizeof(TranspositionTable));
    }
}

#define KILLER_DEPTH 64
int killer_moves[KILLER_DEPTH][2];  

inline const char* get_piece_symbol(uint8_t piece) {
    const char* symbols[] = {" ", "P", "N", "B", "R", "Q", "K"};
    return symbols[piece & 0x07];
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


uint32_t zobrist_table[BOARD_SIZE][32];

void init_zobrist() {
    tt_init();
    
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


inline void tt_init() {
    init_thread_local_tt();
}

inline void tt_store(uint32_t key, int eval, int depth, int flag) {
    if (thread_local_tt == NULL) init_thread_local_tt();
    
    uint32_t idx = key & (TT_SIZE - 1);
    TTEntry* entry = &thread_local_tt->entries[idx];
    
    uint8_t stored_depth = (entry->depth >> 8);
    if (depth > stored_depth || entry->key == 0) {
        entry->key = key;
        entry->eval = eval;
        entry->depth = (depth << 8) | (flag & 0xFF);
    }
}

inline bool tt_lookup(uint32_t key, int depth, int* eval, int* flag) {
    if (thread_local_tt == NULL) init_thread_local_tt();
    
    uint32_t idx = key & (TT_SIZE - 1);
    TTEntry* entry = &thread_local_tt->entries[idx];
    
    if (entry->key == key && (entry->depth >> 8) >= depth) {
        *eval = entry->eval;
        *flag = entry->depth & 0xFF;
        return true;
    }
    return false;
}

inline void tt_clear() {
    if (thread_local_tt == NULL) init_thread_local_tt();
    memset(thread_local_tt->entries, 0, sizeof(thread_local_tt->entries));
}


inline void add_killer(int depth, int move) {
    if (move != killer_moves[depth][0]) {
        killer_moves[depth][1] = killer_moves[depth][0];
        killer_moves[depth][0] = move;
    }
}

inline bool is_killer(int depth, int move) {
    return (move == killer_moves[depth][0] || move == killer_moves[depth][1]);
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


inline int evaluate_fast(const Board* b) {
    int score = 0;
    int vals[] = {0, 1, 3, 3, 5, 9, 0};  
    
    for (int i = 0; i < 64; i++) {
        uint8_t piece = get_piece(b, i);
        if (piece != EMPTY) {
            uint8_t color = piece / 8;
            uint8_t type = piece % 8;
            int v = vals[type];
            
            if (type == P) v += pst_pawn[i] / 4;
            else if (type == N) v += pst_knight[i] / 4;
            
            if (color == BLACK) score += v;
            else score -= v;
        }
    }
    return score;
}


int pvs(Board* b, int depth, int alpha, int beta, bool maximizing, int ply) {
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
            if (i > 3 && moves[i].captured == EMPTY && depth > 2) {
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
            if (i > 3 && moves[i].captured == EMPTY && depth > 2) {
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
        printf("Player 1 move (format: oldrowcol targetrowcol eg: e2 e4): ");
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
            int eval = pvs(b, depth - 1, -INF, INF, false, 0);
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

int main() {
    #ifdef _WIN32
    SetConsoleOutputCP(CP_UTF8);
    #endif
    
    srand(time(NULL));
    init_zobrist();
    init_thread_local_tt();
    
    Board board;
    init_board(&board);
    print_board(&board);
    
    num_threads = select_thread_count();
    printf("Using %d threads\n\n", num_threads);
    
    int difficulty = select_difficulty();
    int search_depth = 6;  
    
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
