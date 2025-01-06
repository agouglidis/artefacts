------------------------------ MODULE HeronABZSafety ------------------------------
EXTENDS TLAPS, Reals

VARIABLES 
x \* A positive initial estimate
    
vars == <<x>>
 
Init == x = 1.45

Next == x' = ( x + 2.0/x ) / 2.0       
        
Spec == Init /\ [][Next]_vars

TypeRealOK == /\ x \in Real 


THEOREM TypeInvariant == Spec => []TypeRealOK
  <1>a. Init => TypeRealOK
    <2> SUFFICES ASSUME Init
                 PROVE  TypeRealOK
      OBVIOUS
    <2> QED
      <3>1. x \in Real
        BY DEF Init, TypeRealOK               
      <3>2. QED
        BY <3>1 DEF TypeRealOK
        
  <1>b. TypeRealOK /\ UNCHANGED vars => TypeRealOK'
    <2> SUFFICES ASSUME TypeRealOK /\ UNCHANGED vars
                 PROVE  TypeRealOK'
      OBVIOUS
    <2> QED
      BY DEF TypeRealOK, vars
    
  <1>c. TypeRealOK /\ Next => TypeRealOK'
    <2> SUFFICES ASSUME TypeRealOK /\ Next
                 PROVE  TypeRealOK'
      OBVIOUS
    <2> QED
        BY DEF TypeRealOK, Next
            
  <1> QED BY PTL, <1>a, <1>b, <1>c DEF Spec


\* Candidate inductive invariant
IInv == x*x - 2.0 >= 0.0
    
P == /\ x >= 1.4142135623
     /\ x <= 1.45       

\* Prove: (1.) 
\* No unsafe state satifies x*x - S >= 0.0
\* Prove that the invariant implies the safety property

THEOREM TypeRealOK /\ Init /\ IInv => P
    <1> SUFFICES ASSUME TypeRealOK, IInv, Init
        PROVE P
      OBVIOUS
    <1> QED BY Z3 DEF Init, IInv, P, TypeRealOK


THEOREM Spec => []P
    \*Base case:
    <1>1. Init => P
        BY Z3 DEF Init, P

    <1>2. TypeRealOK /\  P /\ [Next]_vars =>  P'
        <2> SUFFICES ASSUME TypeRealOK,
                             P,
                            [Next]_vars
            PROVE   P'
            OBVIOUS
        <2>. USE DEF Init, TypeRealOK, P
            <2>1. CASE Next
                <3>1. P'
                    BY <2>1, Z3, PTL DEF Next
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
    
    <1>. QED  BY <1>1, <1>2, TypeInvariant, PTL DEF Spec        
        

\* Prove (2.) 
\* x*x - S >= 0.0 is an inductive invariant of the system
THEOREM Spec => []IInv

    \* Base case: (0.) Initial case
    <1>1. Init => IInv
        BY Z3 DEF Init, IInv 
  
    \* Induction
    <1>2. TypeRealOK /\  IInv /\ [Next]_vars =>  IInv'
        <2> SUFFICES ASSUME TypeRealOK,
                             IInv,
                            [Next]_vars
            PROVE   IInv'
            OBVIOUS
        <2>. USE DEF Init, TypeRealOK, P, IInv
            <2>1. CASE Next
                <3>1. IInv'
                    BY <2>1 DEF Next
                <3>2. QED
                    BY <3>1
            <2>2. CASE UNCHANGED vars
                BY <2>2 DEF vars
            <2>3. QED
                <3>1. CASE Next
                    BY Z3, <3>1, <2>1, <2>2 DEF Next
                <3>2. CASE UNCHANGED vars
                    BY <3>2, <2>1, <2>2 DEF Next
                <3>3. QED
                    BY <3>1, <3>2
    
    <1>. QED  BY <1>1, <1>2, TypeInvariant, PTL DEF Spec  

=============================================================================
\* Modification History
\* Last modified Fri Jan 03 11:50:36 GMT 2025 by agouglidis
\* Created Thu Oct 10 18:36:27 GMT 2024 by agouglidis
