/*
Exercise 1 (10 points): The current K LAMBDA semantics of mu (in Lesson 8) is
based on substitution, and then letrec is defined as a derived operation using
mu. Give mu a different semantics, as a derived construct by translation into
other LAMBDA constructs, like we defined letrec in Lesson 7. To test it, use
the same definition of letrec in terms of mu (from Lesson 8) and write 3
recursive programs, like the provided factorial-letrec.lambda.
*/

module LAMBDA-SYNTAX
  imports DOMAINS-SYNTAX
  imports ID-SYNTAX

  syntax Val ::= Id
               | "lambda" Id "." Exp
  syntax Exp ::= Val
               | Exp Exp              [strict, left]
               | "(" Exp ")"          [bracket]

  syntax Val ::= Int | Bool
  syntax Exp ::= "-" Int
               > Exp "*" Exp          [strict, left]
               | Exp "/" Exp          [strict]
               | Exp "%" Exp          [strict]
               > Exp "+" Exp          [strict, left]
               > Exp "<=" Exp         [strict]
               | Exp "==" Exp         [strict]

  syntax Exp ::= "if" Exp "then" Exp "else" Exp  [strict(1)]

  syntax Exp ::= "let" Id "=" Exp "in" Exp [macro]
  rule let X = E in E':Exp => (lambda X . E') E

  syntax Exp ::= "letrec" Id Id "=" Exp "in" Exp [macro]
               | "mu" Id "." Exp [macro]
  syntax Id ::= "$x" [token] | "$y" [token] | "$z" [token]
  rule mu F:Id . E:Exp =>
      (lambda $x . ((lambda F . E) (lambda $y . ($x $x $y))))
      (lambda $x . ((lambda F . E) (lambda $y . ($x $x $y))))

  rule letrec F:Id X = E in E' => let F = mu F . lambda X . E in E'
endmodule

module LAMBDA
  imports LAMBDA-SYNTAX
  imports DOMAINS

  syntax Set ::= freeVars( Exp ) [function]
  rule freeVars( _ )            => .Set [owise]
  rule freeVars( V:Id )         => SetItem(V)
  rule freeVars( lambda X . E ) => freeVars( E ) -Set SetItem(X)
  rule freeVars( E1 E2 )        => freeVars(E1) freeVars(E2)
  rule freeVars( E1 * E2 )      => freeVars(E1) freeVars(E2)
  rule freeVars( E1 / E2 )      => freeVars(E1) freeVars(E2)
  rule freeVars( E1 % E2 )      => freeVars(E1) freeVars(E2)
  rule freeVars( E1 + E2 )      => freeVars(E1) freeVars(E2)
  rule freeVars( E1 <= E2 )     => freeVars(E1) freeVars(E2)
  rule freeVars( E1 == E2 )     => freeVars(E1) freeVars(E2)
  rule freeVars( if B then E1 else E2) => freeVars(B) freeVars(E1) freeVars(E2)

  syntax Id ::= freshVar(Id, Int, Set) [function]
  rule freshVar(V, I, S) => #let X = String2Id(Id2String(V) +String Int2String(I)) #in #if X in S #then freshVar(V, I +Int 1, S) #else X #fi

  syntax Exp ::= Exp "[" Exp "/" Id "]" [function]

  rule X:Exp [_ / _] => X [owise]
  rule X [V / X] => V

  rule (lambda Y . E) [_ / Y] => lambda Y . E
  rule (lambda Y . E) [V / X] => lambda Y . (E[V / X]) requires Y =/=K X andBool notBool (Y in freeVars(V))
  rule (lambda Y . E) [V / X] => #let Z = freshVar(Y, 0, freeVars(E) freeVars(V)) #in lambda Z . (E[Z / Y] [V / X])
    requires Y =/=K X andBool Y in freeVars(V)

  rule (E1:Exp E2:Exp) [V / X] => E1[V / X] (E2[V / X])

  rule (E1:Exp *  E2:Exp) [V / X] => E1[V / X] *  (E2[V / X])
  rule (E1:Exp /  E2:Exp) [V / X] => E1[V / X] /  (E2[V / X])
  rule (E1:Exp %  E2:Exp) [V / X] => E1[V / X] %  (E2[V / X])
  rule (E1:Exp +  E2:Exp) [V / X] => E1[V / X] +  (E2[V / X])
  rule (E1:Exp <= E2:Exp) [V / X] => E1[V / X] <= (E2[V / X])
  rule (E1:Exp == E2:Exp) [V / X] => E1[V / X] == (E2[V / X])

  rule (if C then E1 else E2) [V / X] => if C[V / X] then E1[V / X] else (E2[V / X])

  syntax KResult ::= Val

  rule (lambda X:Id . E:Exp) V:Val => E[V / X]

  rule - I => 0 -Int I
  rule I1 * I2 => I1 *Int I2
  rule I1 / I2 => I1 /Int I2
  rule I1 % I2 => I1 %Int I2
  rule I1 + I2 => I1 +Int I2
  rule I1 <= I2 => I1 <=Int I2
  rule I1 == I2 => I1 ==Int I2

  rule if true  then E else _ => E
  rule if false then _ else E => E

endmodule

/*
Test results:

% krun factorial-letrec.lambda 
<k>
  3628800 ~> .K
</k>

% krun fibonacci-letrec.lambda 
<k>
  21 ~> .K
</k>

% krun gcd-letrec.lambda 
<k>
  6 ~> .K
</k>
*/
