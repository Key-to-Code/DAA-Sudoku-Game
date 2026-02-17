import tkinter as tk
from tkinter import messagebox
import heapq
import random
import copy

class BitmaskSolver:
    def __init__(self):
        self.rows = [0] * 9
        self.cols = [0] * 9
        self.boxes = [0] * 9

    def _get_box_index(self, r, c):
        return (r // 3) * 3 + (c // 3)

    def _initialize_masks(self, board):
        self.rows = [0] * 9
        self.cols = [0] * 9
        self.boxes = [0] * 9
        empty_cells = []
        for r in range(9):
            for c in range(9):
                if board[r][c] != 0:
                    val = board[r][c] - 1
                    mask = (1 << val)
                    self.rows[r] |= mask
                    self.cols[c] |= mask
                    self.boxes[self._get_box_index(r, c)] |= mask
                else:
                    empty_cells.append((r, c))
        return empty_cells

    def solve(self, board):
        # Solves and returns the board, or None
        empty_cells = self._initialize_masks(board)
        empty_cells.sort(key=lambda cell: self._count_options(cell[0], cell[1]))
        
        if self._backtrack(board, empty_cells, 0):
            return board
        return None

    def count_solutions(self, board, limit=2):
        # Returns number of solutions found (stops at 'limit')
        self._initialize_masks(board) # Re-init masks for this check
        
        # Note: We don't sort empty_cells here to keep it simple/fast for checking
        empty_cells = [(r, c) for r in range(9) for c in range(9) if board[r][c] == 0]
        return self._backtrack_count(board, empty_cells, 0, limit)

    def _count_options(self, r, c):
        box_idx = self._get_box_index(r, c)
        taken = self.rows[r] | self.cols[c] | self.boxes[box_idx]
        options = 0
        for k in range(9):
            if not (taken & (1 << k)):
                options += 1
        return options

    def _backtrack(self, board, empty_cells, idx):
        if idx == len(empty_cells):
            return True
        r, c = empty_cells[idx]
        box_idx = self._get_box_index(r, c)
        taken = self.rows[r] | self.cols[c] | self.boxes[box_idx]
        for k in range(9):
            mask = 1 << k
            if not (taken & mask):
                board[r][c] = k + 1
                self.rows[r] |= mask; self.cols[c] |= mask; self.boxes[box_idx] |= mask
                
                if self._backtrack(board, empty_cells, idx + 1):
                    return True
                
                self.rows[r] &= ~mask; self.cols[c] &= ~mask; self.boxes[box_idx] &= ~mask
                board[r][c] = 0
        return False

    def _backtrack_count(self, board, empty_cells, idx, limit):
        if idx == len(empty_cells):
            return 1
        
        r, c = empty_cells[idx]
        box_idx = self._get_box_index(r, c)
        taken = self.rows[r] | self.cols[c] | self.boxes[box_idx]
        
        count = 0
        for k in range(9):
            mask = 1 << k
            if not (taken & mask):
                board[r][c] = k + 1
                self.rows[r] |= mask; self.cols[c] |= mask; self.boxes[box_idx] |= mask
                
                count += self._backtrack_count(board, empty_cells, idx + 1, limit)
                
                self.rows[r] &= ~mask; self.cols[c] &= ~mask; self.boxes[box_idx] &= ~mask
                board[r][c] = 0
                
                if count >= limit: # Optimization: Stop if we found enough
                    return count
        return count

class BitmaskSolver:
    def __init__(self):
        self.rows = [0] * 9
        self.cols = [0] * 9
        self.boxes = [0] * 9

    def _get_box_index(self, r, c):
        return (r // 3) * 3 + (c // 3)

    def _initialize_masks(self, board):
        self.rows = [0] * 9
        self.cols = [0] * 9
        self.boxes = [0] * 9
        empty_cells = []
        for r in range(9):
            for c in range(9):
                if board[r][c] != 0:
                    val = board[r][c] - 1
                    mask = (1 << val)
                    self.rows[r] |= mask
                    self.cols[c] |= mask
                    self.boxes[self._get_box_index(r, c)] |= mask
                else:
                    empty_cells.append((r, c))
        return empty_cells

    def solve(self, board):
        # Solves and returns the board, or None
        empty_cells = self._initialize_masks(board)
        empty_cells.sort(key=lambda cell: self._count_options(cell[0], cell[1]))
        
        if self._backtrack(board, empty_cells, 0):
            return board
        return None

    def count_solutions(self, board, limit=2):
        # Returns number of solutions found (stops at 'limit')
        self._initialize_masks(board) # Re-init masks for this check
        
        # We need a simplified backtrack that counts instead of returning
        # Note: We don't sort empty_cells here to keep it simple/fast for checking
        empty_cells = [(r, c) for r in range(9) for c in range(9) if board[r][c] == 0]
        return self._backtrack_count(board, empty_cells, 0, limit)

    def _count_options(self, r, c):
        box_idx = self._get_box_index(r, c)
        taken = self.rows[r] | self.cols[c] | self.boxes[box_idx]
        options = 0
        for k in range(9):
            if not (taken & (1 << k)):
                options += 1
        return options

    def _backtrack(self, board, empty_cells, idx):
        if idx == len(empty_cells):
            return True
        r, c = empty_cells[idx]
        box_idx = self._get_box_index(r, c)
        taken = self.rows[r] | self.cols[c] | self.boxes[box_idx]
        for k in range(9):
            mask = 1 << k
            if not (taken & mask):
                board[r][c] = k + 1
                self.rows[r] |= mask; self.cols[c] |= mask; self.boxes[box_idx] |= mask
                
                if self._backtrack(board, empty_cells, idx + 1):
                    return True
                
                self.rows[r] &= ~mask; self.cols[c] &= ~mask; self.boxes[box_idx] &= ~mask
                board[r][c] = 0
        return False

    def _backtrack_count(self, board, empty_cells, idx, limit):
        if idx == len(empty_cells):
            return 1
        
        r, c = empty_cells[idx]
        box_idx = self._get_box_index(r, c)
        taken = self.rows[r] | self.cols[c] | self.boxes[box_idx]
        
        count = 0
        for k in range(9):
            mask = 1 << k
            if not (taken & mask):
                board[r][c] = k + 1
                self.rows[r] |= mask; self.cols[c] |= mask; self.boxes[box_idx] |= mask
                
                count += self._backtrack_count(board, empty_cells, idx + 1, limit)
                
                self.rows[r] &= ~mask; self.cols[c] &= ~mask; self.boxes[box_idx] &= ~mask
                board[r][c] = 0
                
                if count >= limit: # Optimization: Stop if we found enough
                    return count
        return count

class SudokuDuel:
    def __init__(self, root):
        self.root = root
        self.root.title("Sudoku Duel — User vs DP AI")
        self.root.geometry("600x750")
        self.root.configure(bg="#ffffff")
        self.root.resizable(False, False)

        # Game state
        self.board = [[0]*9 for _ in range(9)]
        self.initial_board = [[0]*9 for _ in range(9)]
        self.solution_board = [[0]*9 for _ in range(9)]
        self.cells = [[None]*9 for _ in range(9)]

        self.current_turn = "user"
        self.game_over = False
        self.difficulty = "Medium"
        self.difficulty_var = tk.StringVar(value=self.difficulty)

        self.pq = []
        self.pq_entries = set()

        self.create_widgets()
        self.new_game()

    # --------------------------------------------------
    # GUI
    # --------------------------------------------------

    def create_widgets(self):
        self.status_label = tk.Label(self.root, text="User's Turn",
                                     font=("Helvetica", 14, "bold"),
                                     bg="#ffffff")
        self.status_label.pack(pady=10)

        difficulty_frame = tk.Frame(self.root, bg="#ffffff")
        difficulty_frame.pack(pady=5)

        tk.Label(difficulty_frame, text="Difficulty:",
                 font=("Helvetica", 12),
                 bg="#ffffff").pack(side=tk.LEFT, padx=5)

        for level in ("Easy", "Medium", "Hard"):
            tk.Radiobutton(
                difficulty_frame,
                text=level,
                value=level,
                variable=self.difficulty_var,
                bg="#ffffff",
                command=self.on_difficulty_change
            ).pack(side=tk.LEFT, padx=5)

        board_frame = tk.Frame(self.root, bg="#d0d0d0", bd=4, relief=tk.SUNKEN)
        board_frame.pack(pady=10)

        for i in range(9):
            for j in range(9):
                pady_top = 2 if i % 3 == 0 and i != 0 else 0
                padx_left = 2 if j % 3 == 0 and j != 0 else 0

                cell = tk.Entry(board_frame, width=3,
                                font=("Helvetica", 20, "bold"),
                                justify="center",
                                bd=1, relief=tk.SOLID,
                                bg="white",
                                disabledbackground="white",
                                disabledforeground="black")

                cell.grid(row=i, column=j,
                          padx=(padx_left, 0),
                          pady=(pady_top, 0))

                cell.bind("<KeyRelease>",
                          lambda e, r=i, c=j: self.on_cell_edit(r, c))

                self.cells[i][j] = cell

        button_frame = tk.Frame(self.root, bg="#ffffff")
        button_frame.pack(pady=20)

        self.strict_var = tk.BooleanVar(value=False)
        tk.Checkbutton(self.root,
                       text="Strict Mode (Correct Only)",
                       variable=self.strict_var,
                       bg="#ffffff").pack(pady=5)

        tk.Button(button_frame, text="New Game",
                  command=self.new_game,
                  font=("Helvetica", 12),
                  bg="#4CAF50",
                  fg="white").grid(row=0, column=0, padx=5)

        tk.Button(button_frame, text="Hint",
                  command=self.show_hint,
                  font=("Helvetica", 12),
                  bg="#2196F3",
                  fg="white").grid(row=0, column=1, padx=5)

        tk.Button(button_frame, text="AI Play",
                  command=self.ai_turn,
                  font=("Helvetica", 12),
                  bg="#f44336",
                  fg="white").grid(row=0, column=2, padx=5)

        tk.Button(button_frame, text="Reset",
                  command=self.reset_board,
                  font=("Helvetica", 12),
                  bg="#FF9800",
                  fg="white").grid(row=0, column=3, padx=5)

    # --------------------------------------------------
    # Puzzle Generation
    # --------------------------------------------------

    def on_difficulty_change(self):
        self.difficulty = self.difficulty_var.get()
        self.new_game()

    def generate_puzzle(self):
        # 1. Start with a full valid board
        full_board = self.shuffle_board(self.get_base_pattern())
        self.solution_board = copy.deepcopy(full_board)
        self.board = copy.deepcopy(full_board)

        # 2. Define attempts based on difficulty
        # Higher difficulty = we try to remove more numbers
        if self.difficulty == "Easy":
            target_holes = 30
        elif self.difficulty == "Medium":
            target_holes = 45
        else:
            target_holes = 55 # Very Hard

        cells = [(r, c) for r in range(9) for c in range(9)]
        random.shuffle(cells)
        
        solver = BitmaskSolver()
        holes = 0

        for r, c in cells:
            if holes >= target_holes:
                break
            
            # Save value
            backup = self.board[r][c]
            self.board[r][c] = 0
            
            # Check if unique (we pass a copy so we don't mess up masks)
            # We assume the user wants strictly 1 solution
            solutions = solver.count_solutions(copy.deepcopy(self.board), limit=2)
            
            if solutions != 1:
                # If 0 solutions (impossible) or >1 solutions (ambiguous), revert
                self.board[r][c] = backup
            else:
                holes += 1

        return self.board

    def get_base_pattern(self):
        def pattern(r, c):
            return (3 * (r % 3) + r // 3 + c) % 9
        nums = list(range(1, 10))
        random.shuffle(nums)
        return [[nums[pattern(r, c)] for c in range(9)] for r in range(9)]

    def shuffle_board(self, board):
        for i in range(0, 9, 3):
            block = board[i:i+3]
            random.shuffle(block)
            board[i:i+3] = block
        board = list(map(list, zip(*board)))
        for i in range(0, 9, 3):
            block = board[i:i+3]
            random.shuffle(block)
            board[i:i+3] = block
        board = list(map(list, zip(*board)))
        return board


    

    # --------------------------------------------------
    # DP SOLVER (Bitmasking + MRV)
    # --------------------------------------------------

    def solve_dp(self, board_snapshot):
        """
        Solves the Sudoku puzzle using a high-performance Bitmasking approach.
        
        This method acts as a wrapper for the `BitmaskSolver` class. It employs 
        State Compression (representing row/col/box constraints as integer bits) 
        instead of Set objects. This is a foundational technique in Dynamic 
        Programming (DP) for state representation, offering significantly faster 
        performance than standard backtracking.

        Algorithm Strategy:
        1. State Compression: Converts board constraints into 3 arrays of integers 
           (rows, cols, boxes), where the Nth bit represents the Nth number.
        2. MRV Heuristic: The solver internally sorts empty cells by the number 
           of valid options (Minimum Remaining Values) to prune the search tree early.
        3. Backtracking: Recursively fills cells using bitwise operations for 
           O(1) constant-time validity checks.

        Args:
            board_snapshot (list[list[int]]): A snapshot of the current board state.

        Returns:
            list[list[int]] | None: The fully solved board grid if a solution exists, 
                                    otherwise None.
        """
        # Instantiate the high-performance Bitmask solver
        solver = BitmaskSolver()
        
        # Create a deep copy to prevent the solver's internal state mutations 
        # from affecting the live UI board before a solution is confirmed.
        board_copy = copy.deepcopy(board_snapshot)
        
        result = solver.solve(board_copy)
        return result

    
    # --------------------------------------------------
    # AI Logic
    # --------------------------------------------------

    def ai_turn(self):
        if self.game_over:
            return

        # 1. Analyze the board incrementally for logical deductions
        solver = BitmaskSolver()
        solver._initialize_masks(self.board)
        
        best_cell = None
        min_options = 10
        best_val = None
        
        # Scan for the most constrained cell (Minimum Remaining Values heuristic)
        for r in range(9):
            for c in range(9):
                if self.board[r][c] == 0:
                    options_count = solver._count_options(r, c)
                    if options_count < min_options:
                        min_options = options_count
                        best_cell = (r, c)
                        
        if not best_cell:
            return # Board is full
            
        r, c = best_cell
        
        # 2. Determine the AI's play based on its deductions
        if min_options == 0:
            messagebox.showinfo("Game Over", "No solution exists from this state. A wrong move was played!")
            return
            
        elif min_options == 1:
            # TRUE INCREMENTAL SOLVE: The AI plays a Naked Single 
            box_idx = solver._get_box_index(r, c)
            taken = solver.rows[r] | solver.cols[c] | solver.boxes[box_idx]
            for k in range(9):
                if not (taken & (1 << k)):
                    best_val = k + 1
                    break
        else:
            # FALLBACK: If there are no obvious 1-option deductions, pick the cell with 
            # the fewest options and use DP to ensure we stay on a valid solve path.
            solved = self.solve_dp(self.board)
            if not solved:
                messagebox.showinfo("Game Over", "No solution exists from this state.")
                return
            best_val = solved[r][c]

        # 3. Apply the Move
        self.board[r][c] = best_val
        self.cells[r][c].delete(0, tk.END)
        self.cells[r][c].insert(0, str(best_val))
        self.cells[r][c].config(fg="red")

        if self.is_complete():
            self.game_over = True
            messagebox.showinfo("Game Over", "Puzzle Complete!")

    # --------------------------------------------------
    # User Interaction
    # --------------------------------------------------

    def on_cell_edit(self, row, col):
        if self.game_over or self.initial_board[row][col] != 0:
            return

        cell = self.cells[row][col]
        v = cell.get().strip()

        if v == "":
            self.board[row][col] = 0
            return

        try:
            num = int(v)
            if not (1 <= num <= 9):
                raise ValueError

            if self.strict_var.get():
                if num != self.solution_board[row][col]:
                    messagebox.showerror("Incorrect",
                                         "Strict Mode: Wrong value.")
                    cell.delete(0, tk.END)
                    return

            self.board[row][col] = num
            cell.config(fg="blue")

            if self.is_complete():
                self.game_over = True
                messagebox.showinfo("Game Over", "You Win!")
            else:
                self.ai_turn()
        except ValueError:
            cell.delete(0, tk.END)

    def is_complete(self):
        """Check if the board is fully filled AND is a valid Sudoku solution."""
        for i in range(9):
            for j in range(9):
                if self.board[i][j] == 0:
                    return False

        for i in range(9):
            if len(set(self.board[i])) != 9:
                return False

        for j in range(9):
            col = {self.board[i][j] for i in range(9)}
            if len(col) != 9:
                return False

        for br in range(0, 9, 3):
            for bc in range(0, 9, 3):
                box = set()
                for i in range(br, br + 3):
                    for j in range(bc, bc + 3):
                        box.add(self.board[i][j])
                if len(box) != 9:
                    return False

        return True

    # --------------------------------------------------

    def new_game(self):
        self.game_over = False
        self.board = self.generate_puzzle()
        self.initial_board = copy.deepcopy(self.board)
        self.render_board()
        self.status_label.config(
            text=f"User's Turn ({self.difficulty})"
        )

    def render_board(self):
        for i in range(9):
            for j in range(9):
                cell = self.cells[i][j]
                cell.config(state="normal")
                cell.delete(0, tk.END)

                if self.board[i][j] != 0:
                    cell.insert(0, str(self.board[i][j]))
                    if self.initial_board[i][j] != 0:
                        cell.config(fg="black", state="disabled")
                    else:
                        cell.config(fg="blue")

    def show_hint(self):
        solved = self.solve_dp(self.board)
        if not solved:
            return

        for r in range(9):
            for c in range(9):
                if self.board[r][c] == 0:
                    messagebox.showinfo(
                        "Hint",
                        f"Row {r+1}, Col {c+1} = {solved[r][c]}"
                    )
                    return

    def reset_board(self):
        self.board = copy.deepcopy(self.initial_board)
        self.game_over = False
        self.render_board()


if __name__ == "__main__":
    root = tk.Tk()
    SudokuDuel(root)
    root.mainloop()