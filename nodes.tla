------------------------------- MODULE nodes -------------------------------
EXTENDS Integers, TLC

VARIABLE node

Init == node \in {"A1", "A2", "A3"}

e == \/ node = "A1" /\ node' = "B1"
     \/ node = "A1" /\ node' = "B2"
     \/ node = "A2" /\ node' = "B2"

f == \/ node = "A1" /\ node' = "B1"
     \/ node = "A1" /\ node' = "B2"
     \/ node = "A2" /\ node' = "B2"
     \/ node = "A3" /\ node' = "B2"

g == \/ node = "A1" /\ node' = "C1"
     \/ node = "A2" /\ node' = "B2"
     \/ node = "A3" /\ node' = "B3"

h == \/ node = "A1" /\ node' = "C1"
     \/ node = "A2" /\ node' = "B2"

Next == \/ e
        \/ f
        \/ g
        \/ h

=============================================================================