----------------------------- MODULE CarLights -----------------------------
EXTENDS FiniteSets

set ++ x == set \union {x}
set -- x == set \ {x}

CONSTANTS Light, Gear, Key, PitmanArm, LightRotarySwitch, SteeringWheel
ASSUME IsFiniteSet(Light)
ASSUME IsFiniteSet(Gear)
ASSUME IsFiniteSet(Key)
ASSUME IsFiniteSet(PitmanArm)
ASSUME IsFiniteSet(LightRotarySwitch)
ASSUME IsFiniteSet(SteeringWheel)

Blinking == CHOOSE Blinking : Blinking \notin BOOLEAN
LightState == BOOLEAN ++ Blinking

VARIABLES ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel

vars == << ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel >>

TypeInvariant == /\ ambientLight \in BOOLEAN
                 /\ driver \in BOOLEAN
                 /\ lights \in [Light -> LightState]
                 /\ gear \in Gear
                 /\ pitmanArm \in PitmanArm
                 /\ lightRotarySwitch \in LightRotarySwitch
                 /\ steeringWheel \in SteeringWheel

Init == /\ ambientLight \in BOOLEAN
        /\ driver \in BOOLEAN
        /\ lights = [ Light |-> FALSE ]
        /\ gear \in Gear
        /\ pitmanArm \in PitmanArm
        /\ lightRotarySwitch \in LightRotarySwitch
        /\ steeringWheel \in SteeringWheel
        
SysNext == UNCHANGED vars   (* \/ A  sensor change *)
EnvNext == UNCHANGED vars   (* \/ B  light change *)
Next == SysNext \/ EnvNext
        
Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeInvariant
=============================================================================
\* Modification History
\* Last modified Mon Jan 13 22:20:19 WET 2020 by herulume
\* Created Mon Jan 13 20:57:38 WET 2020 by herulume
