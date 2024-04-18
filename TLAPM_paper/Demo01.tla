------------------------------- MODULE Demo01 -------------------------------
EXTENDS TLAPS, Reals

(*
 *   Description: Example of a discrete-time dynamic system. 
 *   
 *   System: x(t+1) = 2*x(t)/3 + y(t)/2,
 *           y(t+1) = x(t)/2 - y(t)/3.
 *   
 *   The system can be initialised from any state satisfying  x^2 + y^2 <= 1, 
 *   which is our candidate inductive invariant. 
 *   
 *   Needs to show:
 *     (0.) Initial case: Trivial given the inductive invariant 
 *     (1.) No unsafe state satisfies x^2 + y^2 <= 1:
 *          Prove that the invariant implies the safety of the system
 *          i.e., \A x, y \in Real: (x^2 + y^2 <= 1) => (x<= 1 /\ x >= -1)
 *     (2.) x^2 + y^2 <= 1 is an inductive invariant of the system:
 *          Prove that all set of states satisfying x^2 + y^2 <= 1
 *          is closed under the dynamics of the system.
 *
 *)



VARIABLES x, y  

vars == << x, y >>

TypeInvariant == /\ x \in Real
                 /\ y \in Real

\* Initialise variables: x(0)^2 + y(0)^2 <= 1
Init == /\ x = 0.0
        /\ y = 1.0

Next == /\ x' = (2.0 / 3.0) * x  +  0.5 * y
        /\ y' = 0.5 * x - (1.0 / 3.0) * y 
        
Spec == Init /\ [][Next]_vars\* /\ WF_vars(Next)


\* Prove type invariance
THEOREM TypeCorrectness == Spec => []TypeInvariant 
    
    <1>1. Init => TypeInvariant
        <2>. SUFFICES ASSUME Init
            PROVE  TypeInvariant
            OBVIOUS
        <2>. QED
            <3>1. x \in Real
                BY DEF Init, TypeInvariant
            <3>2. y \in Real
                BY DEF Init, TypeInvariant                       
            <3>3. QED
                BY <3>1, <3>2 DEF TypeInvariant

    <1>2. TypeInvariant /\ UNCHANGED vars => TypeInvariant'
        <2>. SUFFICES ASSUME TypeInvariant /\ UNCHANGED vars
            PROVE  TypeInvariant'
            OBVIOUS
        <2>. QED
            BY DEF TypeInvariant, vars
    
    <1>3. TypeInvariant /\ Next => TypeInvariant'
        <2>. SUFFICES ASSUME TypeInvariant /\ Next
            PROVE  TypeInvariant'
            OBVIOUS
        <2>. QED
            BY DEF TypeInvariant, Next
      
    <1> QED BY PTL, <1>1, <1>2, <1>3 DEF Spec


\* Safety property
P == /\ x >= -1.0
     /\ x <= 1.0

\* Our candidate inductive invariant of the system
IInv == x*x + y*y <= 1.0

\* Prove (1.) 
THEOREM TypeInvariant /\ IInv => P 
    <1> SUFFICES ASSUME TypeInvariant, IInv
        PROVE P
    OBVIOUS
    <1> QED BY Z3 DEF IInv, P, TypeInvariant 


\* Prove (2.) 
THEOREM Spec => []IInv

    \* Base case: (0.)
    <1>1. Init => IInv
        BY DEF Init, IInv 
  
    \* Induction
    <1>2. TypeInvariant /\  IInv /\ [Next]_vars =>  IInv'
        <2> SUFFICES ASSUME TypeInvariant,
                             IInv,
                            [Next]_vars
            PROVE   IInv'
            OBVIOUS
        <2>. USE DEF Init, TypeInvariant, P, IInv
            <2>1. CASE Next
                <3>1. IInv'
                    BY <2>1 DEF Next
                <3>2. QED
                    BY <3>1
    
            <2>2. CASE UNCHANGED vars
                BY <2>2 DEF vars
            <2>3. QED
                <3>1. CASE Next
                    BY <3>1, <2>1, <2>2 DEF Next
                <3>2. CASE UNCHANGED vars
                    BY <3>2, <2>1, <2>2 DEF Next
                <3>3. QED
                    BY <3>1, <3>2
    
    <1>. QED  BY <1>1, <1>2, TypeCorrectness, PTL DEF Spec
    
=============================================================================
\* Modification History
\* Last modified Mon Mar 25 08:11:14 GMT 2024 by agouglidis
\* Created Thu Mar 14 19:51:52 GMT 2024 by agouglidis

