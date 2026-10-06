/*
Exercise 3 (10 points): Mofify IMP so that the K "followed by" arrow, ~>, does
not explicitly occur in the definition (it currently occurs in the semantics of
sequential composition). Hint: make sequential composition strict(1) or
seqstrict, and have statements reduce to {} instead of ., ... and don't forget
to make {} a KResult (you may need a new syntactic category for that, which
only includes {} and is included in KResult).

Note: See the purely-syntactic exercise in the nightly built for details and
test programs:

Modify IMP so that the K followed by arrow, ~>, does not explicitly occur in
the definition (it currently occurs in the semantics of sequential
composition).

Hint: make sequential composition strict(1) or seqstrict, and have statements
reduce to {} instead of .; and don't forget to make {} a KResult (you may need
a new syntactic category for that, which only includes {} and is included in
KResult).
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
  syntax EmptyBlock ::= "{" "}"
  syntax Block ::= EmptyBlock
                 | "{" Stmt "}"
  syntax Stmt  ::= Block
                 | Id "=" AExp ";"            [strict(2)]
                 | "if" "(" BExp ")"
                   Block "else" Block         [strict(1)]
                 | "while" "(" BExp ")" Block
                 > Stmt Stmt                  [left, strict(1)]
  syntax Pgm ::= "int" Ids ";" Stmt
  syntax Ids ::= List{Id,","}
endmodule


module IMP
  imports IMP-SYNTAX
  imports DOMAINS
  syntax KResult ::= Int | Bool | EmptyBlock

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
  rule {} S:Stmt => S
  rule {S} => S
// Stmt
  rule <k> X = I:Int; => {} ...</k> <state>... X |-> (_ => I) ...</state>
  rule if (true)  S else _ => S
  rule if (false) _ else S => S
  rule while (B) S => if (B) {S while (B) S} else {}
// Pgm
  rule <k> int (X,Xs => Xs);_ </k> <state> Rho:Map (.Map => X|->0) </state>
    requires notBool (X in keys(Rho))
  rule int .Ids; S => S

// verification ids
  syntax Id ::= "n"     [token]
              | "sum"   [token]
endmodule

/*
Test results:

% krun tests/collatz.imp
<T>
  <k>
    { } ~> .K
  </k>
  <state>
    m |-> 2
    n |-> 1
    q |-> 1
    r |-> 3
    s |-> 66
  </state>
</T>

% krun tests/primes.imp 
<T>
  <k>
    { } ~> .K
  </k>
  <state>
    i |-> 2
    m |-> 10
    n |-> 11
    q |-> 0
    r |-> 1
    s |-> 4
    t |-> 0
    x |-> 0
    y |-> 20
    z |-> 10
  </state>
</T>

% krun tests/sum.imp   
<T>
  <k>
    { } ~> .K
  </k>
  <state>
    n |-> 0
    sum |-> 5050
  </state>
</T>
*/
