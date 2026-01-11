---------------------- MODULE HourClock ---------------------
EXTENDS Naturals
VARIABLE
    \* @type: Int;
    hr
Init == hr \in (1 .. 12)
Next == hr' = IF hr # 12 THEN hr + 1 ELSE 1
Spec == Init /\ [][Next]_hr
-------------------------------------------------------------
THEOREM Spec => []Init
==============================================================