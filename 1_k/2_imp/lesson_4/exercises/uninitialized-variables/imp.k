/*
Exercise 2 (10 points): Modify the K definition of IMP to not automatically
initialize variables to 0. Instead, declared variables should stay
uninitialized until assigned a value, and the execution should get stuck when
an uninitialized variable is looked up.

Note: See the uninitialized-variables exercise in the nightly built for details
and test programs:

Modify the K definition of IMP to not automatically initialize variables to 0.
Instead, declared variables should stay uninitialized until assigned a value,
and the execution should get stuck when an uninitialized variable is looked up.
Specifically, you should add a new undefined construct of sort K, and
initialize all the declared variables with it.
*/

module IMP-SYNTAX
  imports DOMAINS-SYNTAX
  syntax AExp  ::= Int | Id
                 | "-" Int
                 | AExp "/" AExp              [left, strict]
                 | "(" AExp ")"               [bracket]
                 > AExp "+" AExp              [left, strict]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [seqstrict]
                 | "!" BExp                   [strict]
                 | "(" BExp ")"               [bracket]
                 > BExp "&&" BExp             [left, strict(1)]
  syntax Block ::= "{" "}"
                 | "{" Stmt "}"
  syntax Stmt  ::= Block
                 | Id "=" AExp ";"            [strict(2)]
                 | "if" "(" BExp ")"
                   Block "else" Block         [strict(1)]
                 | "while" "(" BExp ")" Block
                 > Stmt Stmt                  [left]
  syntax Pgm ::= "int" Ids ";" Stmt
  syntax Ids ::= List{Id,","}
endmodule


module IMP
  imports IMP-SYNTAX
  imports DOMAINS
  syntax KItem ::= "undefined"
  syntax KResult ::= Int | Bool

  configuration <T color="yellow">
                  <k color="green"> $PGM:Pgm </k>
                  <state color="red"> .Map </state>
                </T>

// AExp
  rule <k> X:Id => I ...</k> <state>... X |-> I ...</state>
  rule I1 / I2 => I1 /Int I2  requires I2 =/=Int 0
  rule I1 + I2 => I1 +Int I2
  rule - I1 => 0 -Int I1
// BExp
  rule I1 <= I2 => I1 <=Int I2
  rule ! T => notBool T
  rule true && B => B
  rule false && _ => false
// Block
  rule {} => .K
  rule {S} => S
// Stmt
  rule <k> X = I:Int; => .K ...</k>
       <state>... X |-> (_ => I:Int) ...</state>
  rule S1:Stmt S2:Stmt => S1 ~> S2
  rule if (true)  S else _ => S
  rule if (false) _ else S => S
  rule while (B) S => if (B) {S while (B) S} else {}
// Pgm
  rule <k> int (X,Xs => Xs);_ </k>
       <state> Rho:Map (.Map => X|->undefined) </state>
      requires notBool (X in keys(Rho))
  rule int .Ids; S => S

// verification ids
  syntax Id ::= "n"     [token]
              | "sum"   [token]
endmodule

/*
Test result:

% krun tests/undefined-lookup.imp 
<T>
  <k>
    undefined ~> #freezer_+__IMP-SYNTAX_AExp_AExp_AExp1_ ( 1 ~> .K ) ~> #freezer_=_;_IMP-SYNTAX_Stmt_Id_AExp1_ ( z ~> .K ) ~> .K
  </k>
  <state>
    x |-> 1
    y |-> undefined
    z |-> undefined
  </state>
</T>

The use of the uninitialized variable `y` indeed led to an undefined value in
the ~> sequence and caused the program to be stuck.
*/
