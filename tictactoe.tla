------------------------------- MODULE tictactoe -------------------------------
EXTENDS Integers, TLC

N == 2
Players == {"X", "O"}
Tiles == (0..N) \X (0..N)
Token == {" ", "X", "O"}
Board == [Tiles -> Token]

VARIABLES board, turn, result
vars == <<board, turn, result>>

NextPlayer == [X |-> "O", O |-> "X"]

ThreeInARow(B, T) ==
    \/ \E x \in 0..N: \A y \in 0..N: (B[<<x, y>>] = T \/ B[<<y, x>>] = T)
    \/ \A x \in 0..N: B[<<x, x>>] = T
    \/ \A x \in 0..N: B[<<x, N-x>>] = T

Win(B) == ThreeInARow(B, "X")
Lose(B) == ThreeInARow(B, "O")
Draw(B) ==  ~Win(B) /\ ~Lose(B) /\ \A t \in Tiles: B[t] /= " "
Done == Draw(board) \/ Win(board) \/ Lose(board)

PossibleMoves(B) == {x \in Tiles: B[x] = " "}

RECURSIVE GoodMove(_, _)
GoodMove(B, M) ==
    LET B_0 == [B EXCEPT ![M] = "X"] IN
        \/ Win(B_0) \/ Draw(B_0)
        \/ \A counter \in PossibleMoves(B_0):
            LET B_1 == [B_0 EXCEPT ![counter] = "O"] IN
                /\ ~Lose(B_1)
                /\ \E y \in PossibleMoves(B_1):  TLCEval(GoodMove(B_1, y))

Init ==
    /\ board = [t \in Tiles |-> " "]
    /\ turn = "X"
    /\ result = "?"

Move ==
    /\ ~Done
    /\ turn' = NextPlayer[turn]
    /\ UNCHANGED result
    /\ \E x \in PossibleMoves(board):
        /\ board' = [board EXCEPT ![x] = turn]
        /\ turn = "X" => GoodMove(board, x)

X == Move /\ turn = "X"
O == Move /\ turn = "O"
WinGame  == result = "?" /\ Win(board)  /\ result' = "Win"  /\ UNCHANGED <<turn, board>>
LoseGame == result = "?" /\ Lose(board) /\ result' = "Lose" /\ UNCHANGED <<turn, board>>
DrawGame == result = "?" /\ Draw(board) /\ result' = "Draw" /\ UNCHANGED <<turn, board>>
PreventDeadlock == result # "?" /\ UNCHANGED vars

Next ==
    \/ X
    \/ O
    \/ WinGame
    \/ LoseGame
    \/ DrawGame
    \/ PreventDeadlock

Fairness == WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

TypeInvariant ==
    /\ turn \in Players
    /\ board \in Board

OneOutcomeInvariant ==
    /\ Win(board) => (~Lose(board) /\ ~Draw(board))
    /\ Lose(board) => (~Win(board) /\ ~Draw(board))
    /\ Draw(board) => (~Lose(board) /\ ~Win(board))

TerminationLiveness == <>[] Done

CanWinContradiction  == ~Win(board)
CanLoseContradiction == ~Lose(board)
CanDrawContradiction == ~Draw(board)

=============================================================================
