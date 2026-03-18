# cheng-engine (Cheng Chess Engine)

Goofy goober type chess engine in C idk bro good enough I guess

A lightweight, single-file chess engine written in C featuring a Principal Variation Search (PVS) algorithm, transposition tables, and multi-threading support.

## Features

- **Search Algorithm**: Principal Variation Search (PVS) with alpha-beta pruning.
- **Optimization**: Transposition tables with Zobrist hashing for position lookup.
- **Move Ordering**: Captures-first generation and killer move heuristics.
- **Evaluation**: Material counting with piece-square tables for positional awareness.
- **Portability**: Cross-platform support for Windows and POSIX systems.
- **Configuration**: Adjustable search depth and thread count at runtime.

## Compilation

Requires a C compiler with pthread support and the math library.

**Linux / macOS:**
```bash
gcc cheng.c -o cheng -lpthread -lm -O3
```

**Windows (MinGW):**
```bash
gcc cheng.c -o cheng.exe -lpthread -lm -O3
```

## Usage

Run the executable and follow the interactive prompts to configure threads, difficulty, and search depth.

```bash
./cheng
```

**Controls:**
- Input moves in standard algebraic notation (e.g., `e2 e4`).
- Select difficulty levels: Beginner (random), Easy (greedy), or Hard (depth search).

## Architecture

- **Board Representation**: 0x88-style array mapping.
- **Threading**: Uses thread-local storage for transposition tables to prevent race conditions.
- **Memory Management**: Configurable transposition table size via `TT_SIZE` macro to fit available RAM.

## License

This project is provided as-is for educational and development purposes.
