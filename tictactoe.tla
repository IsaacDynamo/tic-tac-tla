------------------------------- MODULE tictactoe -------------------------------
EXTENDS Integers, TLC

N == 2
Players == {"X", "O"}
Tiles == (0..N) \X (0..N)
Token == {" ", "X", "O"}
Board == [Tiles -> Token]

VARIABLES board, turn
vars == <<board, turn>>

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

GoodBoard[B_0 \in Board] ==
    IF Win(B_0) \/ Draw(B_0) THEN TRUE
    ELSE IF Lose(B_0) THEN FALSE
    ELSE \A B_1 \in {[B_0 EXCEPT ![counter] = "O"]: counter \in PossibleMoves(B_0)}:
        IF Lose(B_1) THEN FALSE
        ELSE \E B_2 \in {[B_1 EXCEPT ![y] = "X"]: y \in PossibleMoves(B_1)}:
            TLCEval(GoodBoard[B_2])

Move ==
    /\ turn' = NextPlayer[turn]
    /\ \E x \in PossibleMoves(board):
        /\ board' = [board EXCEPT ![x] = turn]
        /\ turn = "X" => GoodBoard[board']

Init ==
    /\ board = [t \in Tiles |-> " "]
    /\ turn = "X"

Next ==
    \/ ~Done /\ Move
    \/ Done /\ UNCHANGED vars


Fairness == WF_vars(Move)

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
