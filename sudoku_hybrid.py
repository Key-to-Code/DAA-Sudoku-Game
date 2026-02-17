import tkinter as tk
from tkinter import messagebox
import heapq
import random
import copy
import threading
"""
Strategy & Architecture
This implementation constitutes a Hybrid AI Solver designed to solve Sudoku puzzles efficiently by synthesizing two distinct algorithmic strategies: Constraint Propagation (Divide & Conquer) and Backtracking with Bitmasks (Dynamic Programming).

1. Phase 1: Divide & Conquer (Constraint Propagation)
Prior to engaging in complex recursive operations, the AI executes a deterministic initial pass over the board.
Concept: The board is analyzed as nine 3 × 3 sub-grids. The system identifies "Uniquely Determined Cells"—positions where, given the existing row, column, and box constraints, only a single numerical value is mathematically viable.
Execution: The solve_dnc_phase function iterates continuously. The successful allocation of a value to a cell may impose new constraints on adjacent sectors, thereby revealing further deterministic moves. This cycle continues until all trivial solutions are exhausted.

2. Phase 2: Dynamic Programming with Bitmasking
Upon completion of the initial deterministic phase, the AI resolves the remaining complex cells utilizing a recursive search algorithm optimized via bitwise operations.
Bitmasking: To enhance performance, the solver employs integer-based bitmasks rather than set data structures for tracking used digits.
Example: The usage of digits 1 and 4 is represented by the binary sequence 000001001. This method facilitates constraint verification (is_valid) through constant-time (O(1)) bitwise AND/OR operations. This logic is encapsulated within _init_bitmasks and _candidates_bitmask.
MRV Heuristic (Minimum Remaining Values): The AI avoids arbitrary guessing. It deterministically selects the empty cell possessing the fewest possible candidate values for immediate resolution. This strategy significantly minimizes the "branching factor" of the search tree.
Memoization: The solve_dp function caches previously encountered board configurations within self.dp_cache, thereby preventing the redundant computation of identical sub-problems.

3. The "Duel" Logic
The application facilitates a turn-based interaction between the user and the AI.
AI Turn: The AI identifies the cell with the highest priority (via the MRV Priority Queue), computes the solution for the entire board to ascertain the correct value for that specific cell, populates it, and subsequently yields control back to the user.

Function Reference
Initialization & UI
__init__: Initializes the application window, game state variables, and the MRV Priority Queue.
create_widgets: Constructs the grid interface, control buttons, and status indicators.
render_board: Updates the user interface to reflect the current state of self.board, managing cell coloration (blue for user entries, red for AI entries) and style resetting.

Game Logic & Generation
generate_puzzle: constructs a fully solved board, randomizes it, and selectively removes numbers in accordance with the specified difficulty level.
shuffle_board & get_base_pattern: Auxiliary functions for generating a randomized, valid Sudoku grid.
is_valid & get_candidates: Implements standard rule validation to determine if a number is permissible within a given cell.

The Solver (The "Brain")
solve_hybrid: The primary entry point. It orchestrates the execution of Phase 1 (Divide & Conquer) followed by Phase 2 (Dynamic Programming).
solve_dnc_phase & solve_dnc_subgrid: The deterministic solver responsible for populating obvious cells.
solve_dp, _solve_dp_helper: The recursive backtracking solver for complex board states.
_init_bitmasks, _candidates_bitmask: Transforms the board state into a binary representation for efficient processing.
_find_mrv_cell_bitmask: Scans the board to identify the empty cell with the minimal number of potential options.

AI Interaction
initialize_priority_queue: Analyzes the board and populates the self.pq heap with empty cells, prioritized by solution difficulty.
ai_make_move: Retrieves the most constrained cell from the queue, executes the solve_hybrid solver to determine its true value, and updates the board.
ai_turn & ai_play_button: Manages the AI's turn execution sequence while maintaining UI responsiveness.
"""



class SudokuDuel:
    def __init__(self, root):
        self.root = root
        self.root.title("Sudoku Duel — User vs Hybrid D&C+DP AI")
        self.root.geometry("600x750")
        self.root.configure(bg="#ffffff")
        self.root.resizable(False, False)

        self.board = [[0] * 9 for _ in range(9)]
        self.initial_board = [[0] * 9 for _ in range(9)]
        self.solution_board = [[0] * 9 for _ in range(9)]
        self.cells = [[None] * 9 for _ in range(9)]

        self.current_turn = "user"
        self.game_over = False
        self.difficulty = "Medium"
        self.difficulty_var = tk.StringVar(value=self.difficulty)

        # Priority Queue for MRV (Minimum Remaining Values)
        self.pq = []
        self.pq_entries = set()

        self.create_widgets()
        self.new_game()

    def create_widgets(self):
        self.status_label = tk.Label(
            self.root, text="User's Turn",
            font=("Helvetica", 14, "bold"),
            bg="#ffffff", fg="black",
        )
        self.status_label.pack(pady=10)

        difficulty_frame = tk.Frame(self.root, bg="#ffffff")
        difficulty_frame.pack(pady=5)

        tk.Label(
            difficulty_frame, text="Difficulty:",
            font=("Helvetica", 12), bg="#ffffff",
        ).pack(side=tk.LEFT, padx=5)

        for level in ("Easy", "Medium", "Hard"):
            tk.Radiobutton(
                difficulty_frame, text=level, value=level,
                variable=self.difficulty_var, bg="#ffffff",
                command=self.on_difficulty_change,
            ).pack(side=tk.LEFT, padx=5)

        board_frame = tk.Frame(self.root, bg="#d0d0d0", bd=4, relief=tk.SUNKEN)
        board_frame.pack(pady=10)

        # Register validation command for Entry widgets
        vcmd = (self.root.register(self.validate_input), '%P')

        for i in range(9):
            for j in range(9):
                pady_top = 2 if i % 3 == 0 and i != 0 else 0
                padx_left = 2 if j % 3 == 0 and j != 0 else 0

                cell = tk.Entry(
                    board_frame, width=3,
                    font=("Helvetica", 20, "bold"),
                    justify="center", bd=1, relief=tk.SOLID,
                    bg="white", disabledbackground="white",
                    disabledforeground="black",
                    validate="key", validatecommand=vcmd
                )
                cell.grid(row=i, column=j,
                          padx=(padx_left, 0), pady=(pady_top, 0))
                
                # Bind event for logic handling
                cell.bind("<KeyRelease>",
                          lambda e, r=i, c=j: self.on_cell_edit(r, c))
                self.cells[i][j] = cell

        self.strict_var = tk.BooleanVar(value=False)
        tk.Checkbutton(
            self.root, text="Strict Mode (Correct Only)",
            variable=self.strict_var, bg="#ffffff",
        ).pack(pady=5)

        button_frame = tk.Frame(self.root, bg="#ffffff")
        button_frame.pack(pady=20)

        tk.Button(
            button_frame, text="New Game", command=self.new_game,
            font=("Helvetica", 12), bg="#4CAF50", fg="white",
        ).grid(row=0, column=0, padx=5)

        tk.Button(
            button_frame, text="Hint", command=self.show_hint,
            font=("Helvetica", 12), bg="#2196F3", fg="white",
        ).grid(row=0, column=1, padx=5)

        tk.Button(
            button_frame, text="AI Play", command=self.ai_play_button,
            font=("Helvetica", 12), bg="#f44336", fg="white",
        ).grid(row=0, column=2, padx=5)

        tk.Button(
            button_frame, text="Reset", command=self.reset_board,
            font=("Helvetica", 12), bg="#FF9800", fg="white",
        ).grid(row=0, column=3, padx=5)

    def validate_input(self, P):
        """Ensures only digits 1-9 or empty string can be entered."""
        if P == "" or (P.isdigit() and 1 <= int(P) <= 9):
            return True
        return False

    def on_difficulty_change(self):
        self.difficulty = self.difficulty_var.get()
        self.new_game()

    # --- PUZZLE GENERATION ---
    def generate_puzzle(self, difficulty=None):
        if difficulty is None:
            difficulty = self.difficulty

        full_board = self.shuffle_board(self.get_base_pattern())
        self.solution_board = copy.deepcopy(full_board)
        self.board = copy.deepcopy(full_board)

        cells = [(i, j) for i in range(9) for j in range(9)]
        random.shuffle(cells)

        if difficulty == "Easy":
            remove_count = 30
        elif difficulty == "Medium":
            remove_count = 45
        elif difficulty == "Hard":
            remove_count = 55
        else:
            remove_count = 40

        for i in range(remove_count):
            r, c = cells[i]
            self.board[r][c] = 0

        return self.board

    def get_base_pattern(self):
        def pattern(r, c):
            return (3 * (r % 3) + r // 3 + c) % 9
        nums = list(range(1, 10))
        random.shuffle(nums)
        return [[nums[pattern(r, c)] for c in range(9)] for r in range(9)]

    def shuffle_board(self, board):
        # Shuffle rows within blocks
        for i in range(0, 9, 3):
            block = board[i:i + 3]
            random.shuffle(block)
            board[i:i + 3] = block
        
        # Transpose to shuffle columns (as rows)
        board = list(map(list, zip(*board)))
        for i in range(0, 9, 3):
            block = board[i:i + 3]
            random.shuffle(block)
            board[i:i + 3] = block
        
        # Transpose back
        board = list(map(list, zip(*board)))
        return board

    # --- VALIDATION & HELPERS ---
    def is_valid(self, board, row, col, num):
        for i in range(9):
            if board[row][i] == num and i != col: return False
            if board[i][col] == num and i != row: return False
        br, bc = 3 * (row // 3), 3 * (col // 3)
        for i in range(br, br + 3):
            for j in range(bc, bc + 3):
                if board[i][j] == num and (i, j) != (row, col): return False
        return True

    def get_candidates(self, board, row, col):
        if board[row][col] != 0:
            return set()
        candidates = set(range(1, 10))
        candidates -= set(board[row])
        candidates -= {board[i][col] for i in range(9)}
        br, bc = 3 * (row // 3), 3 * (col // 3)
        for i in range(br, br + 3):
            for j in range(bc, bc + 3):
                candidates.discard(board[i][j])
        return candidates

    def is_complete(self):
        return all(self.board[i][j] != 0 for i in range(9) for j in range(9))

    # --- SOLVER LOGIC (D&C + DP) ---
    def solve_dnc_subgrid(self, board, sr, sc):
        progress = False
        for r in range(sr, sr + 3):
            for c in range(sc, sc + 3):
                if board[r][c] == 0:
                    cands = self.get_candidates(board, r, c)
                    if len(cands) == 1:
                        board[r][c] = cands.pop()
                        progress = True
        return progress

    def solve_dnc_phase(self, board):
        changed = True
        while changed:
            changed = False
            for box_r in range(0, 9, 3):
                for box_c in range(0, 9, 3):
                    if self.solve_dnc_subgrid(board, box_r, box_c):
                        changed = True

    def _init_bitmasks(self, board):
        self.row_mask = [0] * 9
        self.col_mask = [0] * 9
        self.box_mask = [0] * 9
        for r in range(9):
            for c in range(9):
                if board[r][c] != 0:
                    bit = 1 << (board[r][c] - 1)
                    self.row_mask[r] |= bit
                    self.col_mask[c] |= bit
                    self.box_mask[(r // 3) * 3 + c // 3] |= bit

    def _candidates_bitmask(self, board, row, col):
        if board[row][col] != 0: return 0
        box_id = (row // 3) * 3 + col // 3
        used = self.row_mask[row] | self.col_mask[col] | self.box_mask[box_id]
        return (~used) & 0x1FF

    def _bitmask_to_set(self, mask):
        digits = set()
        for d in range(9):
            if mask & (1 << d): digits.add(d + 1)
        return digits

    def _find_mrv_cell_bitmask(self, board):
        best = None
        best_count = 10
        for r in range(9):
            for c in range(9):
                if board[r][c] == 0:
                    mask = self._candidates_bitmask(board, r, c)
                    count = bin(mask).count("1")
                    if count == 0: return (r, c, set()) # Unsolvable path
                    if count < best_count:
                        best_count = count
                        best = (r, c, self._bitmask_to_set(mask))
                        if best_count == 1: return best
        return best

    def solve_dp(self, board):
        self.dp_cache = {}
        self._init_bitmasks(board)
        return self._solve_dp_helper(board)

    def _solve_dp_helper(self, board):
        state = tuple(tuple(row) for row in board)
        if state in self.dp_cache: return self.dp_cache[state]

        mrv = self._find_mrv_cell_bitmask(board)
        if mrv is None:
            self.dp_cache[state] = board
            return board

        row, col, candidates = mrv
        if not candidates:
            self.dp_cache[state] = None
            return None

        box_id = (row // 3) * 3 + col // 3
        for num in candidates:
            bit = 1 << (num - 1)
            board[row][col] = num
            self.row_mask[row] |= bit
            self.col_mask[col] |= bit
            self.box_mask[box_id] |= bit

            result = self._solve_dp_helper(board)
            if result:
                self.dp_cache[state] = result
                return result

            board[row][col] = 0
            self.row_mask[row] &= ~bit
            self.col_mask[col] &= ~bit
            self.box_mask[box_id] &= ~bit

        self.dp_cache[state] = None
        return None

    def solve_hybrid(self, board_snapshot):
        board = copy.deepcopy(board_snapshot)
        self.solve_dnc_phase(board)
        solved = self.solve_dp(board)
        return solved

    # --- AI & GAMEPLAY LOGIC ---
    def initialize_priority_queue(self):
        self.pq = []
        self.pq_entries = set()
        for i in range(9):
            for j in range(9):
                if self.board[i][j] == 0:
                    c = self.get_candidates(self.board, i, j)
                    if c:
                        heapq.heappush(self.pq, (len(c), i, j))
                        self.pq_entries.add((i, j))

    def update_neighbors(self, row, col):
        """Updates priorities of neighbors after a move."""
        neighbours = set()
        for i in range(9):
            neighbours.add((row, i))
            neighbours.add((i, col))
        br, bc = 3 * (row // 3), 3 * (col // 3)
        for i in range(br, br + 3):
            for j in range(bc, bc + 3):
                neighbours.add((i, j))

        for r, c in neighbours:
            if self.board[r][c] == 0 and (r, c) != (row, col):
                cand = self.get_candidates(self.board, r, c)
                # We simply push to heap; lazy deletion handles stale entries later
                if cand:
                    heapq.heappush(self.pq, (len(cand), r, c))
                    self.pq_entries.add((r, c))

    def ai_make_move(self):
        # Clean stale entries from PQ
        while self.pq and self.board[self.pq[0][1]][self.pq[0][2]] != 0:
            _, r, c = heapq.heappop(self.pq)
            self.pq_entries.discard((r, c))

        # FIX: If PQ is empty but board is incomplete, re-scan
        if not self.pq and not self.is_complete():
            self.initialize_priority_queue()

        if not self.pq:
            return False

        _, row, col = heapq.heappop(self.pq)
        self.pq_entries.discard((row, col))

        solved_board = self.solve_hybrid(self.board)

        if solved_board:
            correct_val = solved_board[row][col]
            self.board[row][col] = correct_val

            self.cells[row][col].config(state="normal")
            self.cells[row][col].delete(0, tk.END)
            self.cells[row][col].insert(0, str(correct_val))
            
            # AI Move coloring
            self.cells[row][col].config(fg="red", disabledforeground="red", state="disabled")

            self.update_neighbors(row, col)
            return True
        else:
            return False

    def ai_play_button(self):
        if self.game_over: return
        self.status_label.config(text="AI is Thinking...")
        self.root.update_idletasks()
        
        # Use a tiny delay to allow UI to update label before calculation freezes it
        self.root.after(100, self.ai_turn)

    def ai_turn(self):
        if self.game_over: return

        if not self.ai_make_move():
            if self.is_complete():
                self.game_over = True
                messagebox.showinfo("Game Over", "Puzzle Complete!")
            else:
                messagebox.showinfo("Game Over", "AI cannot find a solution (unsolvable state).")
                self.new_game()
            return

        if self.is_complete():
            self.game_over = True
            messagebox.showinfo("Game Over", "Puzzle Complete! AI Finished it.")
            return

        self.current_turn = "user"
        self.status_label.config(text="User's Turn")

    def on_cell_edit(self, row, col):
        if self.game_over: return
        # Prevent editing initial fixed cells (safety check)
        if self.initial_board[row][col] != 0: return

        cell = self.cells[row][col]
        v = cell.get().strip()

        # FIX: Handle Deletion
        if v == "":
            self.board[row][col] = 0
            # Re-add to queue because it is now an empty cell needing solution
            self.initialize_priority_queue() 
            return

        try:
            num = int(v)
            if not (1 <= num <= 9): raise ValueError

            if self.strict_var.get():
                if num != self.solution_board[row][col]:
                    messagebox.showerror("Incorrect", "Strict Mode: Wrong value.")
                    cell.delete(0, tk.END)
                    self.board[row][col] = 0
                    return

            if self.is_valid(self.board, row, col, num):
                self.board[row][col] = num
                self.pq_entries.discard((row, col))
                self.update_neighbors(row, col)
                cell.config(fg="blue")

                if self.is_complete():
                    self.game_over = True
                    messagebox.showinfo("Game Over", "Puzzle Complete! You Win!")
                    return

                # Trigger AI Turn
                self.current_turn = "ai"
                self.status_label.config(text="AI is Thinking...")
                self.root.after(300, self.ai_turn)
            else:
                # Invalid move (standard rules)
                # You might want to allow it but mark red. 
                # For now, we revert to behavior: delete if invalid.
                cell.delete(0, tk.END)
                self.board[row][col] = 0
        except ValueError:
            cell.delete(0, tk.END)

    def new_game(self):
        self.game_over = False
        self.board = self.generate_puzzle()
        self.initial_board = copy.deepcopy(self.board)
        self.current_turn = "user"
        self.initialize_priority_queue()
        self.render_board()
        self.status_label.config(text=f"User's Turn ({self.difficulty})")

    def render_board(self):
        # FIX: Aggressively reset all styles before applying state
        for i in range(9):
            for j in range(9):
                cell = self.cells[i][j]
                val = self.board[i][j]
                
                # Reset style to default (removes yellow hints, red AI text)
                cell.config(state="normal", bg="white", fg="black", disabledforeground="black")
                cell.delete(0, tk.END)
                
                if val != 0:
                    cell.insert(0, str(val))
                    if self.initial_board[i][j] != 0:
                        # Fixed cell
                        cell.config(state="disabled", disabledforeground="black", font=("Helvetica", 20, "bold"))
                    else:
                        # User/AI filled cell. 
                        # Note: If we want AI moves to stay RED, we need to track who made the move.
                        # For now, we render them blue (user-style) to keep code simple, 
                        # or you can compare against solution_board if strict.
                        cell.config(fg="blue")

    def show_hint(self):
        if self.game_over: return
        
        # Ensure PQ is fresh
        self.initialize_priority_queue()
        
        # Clean stale
        while self.pq and self.board[self.pq[0][1]][self.pq[0][2]] != 0:
            heapq.heappop(self.pq)

        if not self.pq:
            messagebox.showinfo("Hint", "No empty cells remaining!")
            return

        _, row, col = self.pq[0]

        # Reset any previous highlights (by redrawing board)
        self.render_board()

        # Highlight specific cell
        hint_cell = self.cells[row][col]
        hint_cell.config(bg="#ffeb3b") # Yellow highlight

        cand = sorted(self.get_candidates(self.board, row, col))
        messagebox.showinfo(
            "Hint",
            f"Hybrid D&C+DP Target:\nRow {row + 1}, Col {col + 1}\nValid Options: {cand}"
        )
        # The yellow background will be cleared on next render_board call (e.g. next move)

    def reset_board(self):
        # FIX: Complete logic reset
        self.game_over = False
        self.board = copy.deepcopy(self.initial_board)
        self.current_turn = "user"
        self.initialize_priority_queue() # Critical: Reset AI memory
        self.render_board() # Redraw clean board
        self.status_label.config(text="User's Turn")

if __name__ == "__main__":
    root = tk.Tk()
    SudokuDuel(root)
    root.mainloop()