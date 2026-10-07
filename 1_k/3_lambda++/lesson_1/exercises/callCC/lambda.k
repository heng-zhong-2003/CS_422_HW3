/*
Define a variant of `callcc`, say `callCC`, which never returns to the
current context unless a value is specifically passed to its argument
continuation.  Follow a substitution-based style.

Implement callCC: normal return abandons the current context; only explicit
application of the captured continuation resumes that context. Preserve
ordinary callcc. Argument evaluation, function application, bindings, and
invoking an outer continuation from a nested capture are checked. Use either
provided semantic style.
*/

requires "substitution.md"

module LAMBDA-SYNTAX
  imports DOMAINS-SYNTAX
  imports KVAR-SYNTAX

  syntax Val ::= KVar
               | "lambda" KVar "." Exp  [binder]
  syntax Exp ::= Val
               | Exp Exp              [strict, left]
               | "(" Exp ")"          [bracket]

  syntax Val ::= Int | Bool
  syntax Exp ::= "-" Int
               > Exp "*" Exp          [strict, left]
               | Exp "/" Exp          [strict]
               > Exp "+" Exp          [strict, left]
               > Exp "<=" Exp         [strict]

  syntax Exp ::= "if" Exp "then" Exp "else" Exp  [strict(1)]

  syntax Exp ::= "let" KVar "=" Exp "in" Exp [macro]
  rule let X = E in E':Exp => (lambda X . E') E

  syntax Exp ::= "letrec" KVar KVar "=" Exp "in" Exp  [macro]
               | "mu" KVar "." Exp                    [binder]
  rule letrec F:KVar X = E in E' => let F = mu F . lambda X . E in E'

  syntax Exp ::= "callcc" Exp  [strict]
  syntax Val ::= cc(K)

  syntax Exp ::= "callCC" Exp  [strict]
  syntax Val ::= CC(K)
endmodule

module LAMBDA
  imports LAMBDA-SYNTAX
  imports SUBSTITUTION
  imports DOMAINS

  syntax KResult ::= Val

  rule (lambda X:KVar . E:Exp) V:Val => E[V / X]

  rule - I => 0 -Int I
  rule I1 * I2 => I1 *Int I2
  rule I1 / I2 => I1 /Int I2
  rule I1 + I2 => I1 +Int I2
  rule I1 <= I2 => I1 <=Int I2

  rule if true  then E else _ => E
  rule if false then _ else E => E

  rule mu X . E => E[(mu X . E) / X]

  rule <k> (callcc V:Val => V cc(K)) ~> K </k>
  rule <k> cc(K) V ~> _ =>  V ~> K </k>

  rule <k> (callCC V:Val ~> K) => V CC((K)) </k>
  rule <k> CC(K) V ~> _ =>  V ~> K </k>
endmodule
