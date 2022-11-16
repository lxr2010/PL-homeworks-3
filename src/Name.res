module Debru = {
  type rec lambda = 
  | Var(int)
  | Fn(lambda) 
  | App(lambda, lambda)

  let rec toString = (t: lambda): string => switch t {
  | Var(i) => Js.Int.toString(i)
  | Fn(b) => "(λ." ++ toString(b) ++")"
  | App(m, n) => "(" ++ toString(m) ++" " ++ toString(n) ++ ")"
  }

  let print_lambda = l => {
    let print_paren = (b, s) => {
      if b { "(" ++ s ++ ")" } else { s }
    }
    let rec go = (l, p) => {
      switch l {
        | Var(x) => Js.Int.toString(x)
        | Fn(a) => print_paren(p>0, "fun -> " ++ go(a, 0))
        | App(a, b) => print_paren(p>1, go(a, 1) ++ " " ++ go(b, 2))

      }
    }
    go(l, 0)
  }


  // Var(j) becomes Var(i+j) if j >= d
  let rec shift_aux = (i, d, u) => {
    switch u {
    | Var(j) => { if j >= d { Var(i+j) } else { u } }
    | Fn(b) => Fn(shift_aux(i, d+1, b))
    | App(a, b) => 
        App(shift_aux(i, d, a), shift_aux(i, d, b))
    }
  }
  let shift = (i, u) => shift_aux(i, 0, u)

  // t[u/i]: use u to replace Var(i) in term t
  let rec subst = (t, i, u) => {
    switch t {
    | Var(j) => if j == i { u } else { t }
    | Fn(b) => Fn(subst(b, i+1, shift(1, u)))
    | App(a, b) => App(subst(a, i, u), subst(b, i, u))
    }
  }
  
  // Homework: implement the complete interpreter
  let eval = (t: lambda) => {
    let rec evalHelper = (t:lambda) => {
      switch t {
      | Var(_) => t
      | Fn(b) => Fn(evalHelper(b))
      | App(f, arg) => {
        switch evalHelper(f) {
        | Fn(b) => {
          let va = evalHelper(arg)
          let va_shifted = shift(1,va)
          let b_substed = subst(b, 0, va_shifted)
          let b_substed_deshifted = shift(-1, b_substed)
          evalHelper(b_substed_deshifted)
        }
        | k => App(k, evalHelper(arg))
        }
      }
      }
    }
    evalHelper(t)
  }
}

module DebruTest = {
  open! Debru

  let id = Fn(Var(0))
  let trueB = Fn(Fn(Var(1)))
  let falseB = Fn(Fn(Var(0)))
  let zero = Fn(Fn(Var(0)))
  let one = Fn(Fn(App(Var(1),Var(0))))
  let succ = Fn(Fn(Fn(App(Var(1),App(App(Var(2),Var(1)),Var(0))))))
  let pair = Fn(Fn(Fn(App(App(Var(0),Var(2)),Var(1)))))
  let fst = Fn(App(Var(0),trueB))
  let snd = Fn(App(Var(0),falseB))
  let pred = 
  Fn(App(
    fst,App(
      App(
        Var(0),
        Fn(App(
          App(pair,App(snd,Var(0))),
          App(succ,App(snd,Var(0)))))),
      App(App(pair,zero),zero))))
  let toChurchNumB = (n : int) => {
    let rec helper = (n: int, churchNumB: lambda) : lambda => 
      if n < 0 {assert false}
      else {
        switch n {
        | 0 => churchNumB 
        | _ => helper(n-1, App(succ, churchNumB))
        }
      }
    helper(n, zero)
  }

  let test = () => {
    Js.log(print_lambda(eval(App(pred,toChurchNumB(8)))))
  }
}

let _ = DebruTest.test()

// Homework: support let
module DebruLet = {
  type rec lambda = 
  | Var (int)
  | App (lambda, lambda)
  | Fn (lambda)
  | Let (lambda, lambda)

  let rec toString = (t: lambda): string => switch t {
  | Var(i) => Js.Int.toString(i)
  | Fn(b) => "(λ." ++ toString(b) ++")"
  | App(m, n) => "(" ++ toString(m) ++" " ++ toString(n) ++ ")"
  | Let(l, b) => "(" ++ toString(l) ++ "->" ++ toString(b) ++ ")"
  }

  let print_lambda = l => {
    let print_paren = (b, s) => {
      if b { "(" ++ s ++ ")" } else { s }
    }
    let rec go = (l, p) => {
      switch l {
        | Var(x) => Js.Int.toString(x)
        | Fn(a) => print_paren(p>0, "fun -> " ++ go(a, 0))
        | App(a, b) => print_paren(p>1, go(a, 1) ++ " " ++ go(b, 2))
        | Let(l, b) => print_paren(p>1, "let " ++ go(l,1) ++ " in " ++ go(b, 2))
      }
    }
    go(l, 0)
  }


  // Var(j) becomes Var(i+j) if j >= d
  let rec shift_aux = (i, d, u) => {
    switch u {
    | Var(j) => { if j >= d { Var(i+j) } else { u } }
    | Fn(b) => Fn(shift_aux(i, d+1, b))
    | App(a, b) => 
        App(shift_aux(i, d, a), shift_aux(i, d, b))
    | Let(l, b) => shift_aux(i,d,App(Fn(b),l))
    }
  }
  let shift = (i, u) => shift_aux(i, 0, u)

  // t[u/i]: use u to replace Var(i) in term t
  let rec subst = (t, i, u) => {
    switch t {
    | Var(j) => if j == i { u } else { t }
    | Fn(b) => Fn(subst(b, i+1, shift(1, u)))
    | App(a, b) => App(subst(a, i, u), subst(b, i, u))
    | Let(l, b) => subst(App(Fn(b),l),i,u)
    }
  }

// eval Let(l1, l2) == eval App((lambda.l2),l1)
  let eval = (t: lambda) => {
    let rec evalHelper = (t:lambda) => {
      switch t {
      | Var(_) => t
      | Fn(b) => Fn(evalHelper(b))
      | Let(loc, body) => evalHelper(App(Fn(body),loc))
      | App(f, arg) => {
        switch evalHelper(f) {
        | Fn(b) => {
          let va = evalHelper(arg)
          let va_shifted = shift(1,va)
          let b_substed = subst(b, 0, va_shifted)
          let b_substed_deshifted = shift(-1, b_substed)
          evalHelper(b_substed_deshifted)
        }
        | k => App(k, evalHelper(arg))
        }
      }
      }
    }
    evalHelper(t)
  }
}

module DebruLetTest = {
  open! DebruLet


  let id = Fn(Var(0))
  let trueB = Fn(Fn(Var(1)))
  let falseB = Fn(Fn(Var(0)))
  let zero = Fn(Fn(Var(0)))
  let one = Fn(Fn(App(Var(1),Var(0))))
  let succ = Fn(Fn(Fn(App(Var(1),App(App(Var(2),Var(1)),Var(0))))))
  let pair = Fn(Fn(Fn(App(App(Var(0),Var(2)),Var(1)))))
  let fst = Fn(App(Var(0),trueB))
  let snd = Fn(App(Var(0),falseB))
  let pred = Let(
                Fn(App(
                  App(pair,App(snd,Var(0))),
                  App(succ,App(snd,Var(0))))),
                Let(
                  App(App(pair,zero),zero),
                  Fn(App(fst,App(App(Var(0),Var(2)),Var(1))))
          ))
  let toChurchNumB = (n : int) => {
    let rec helper = (n: int, churchNumB: lambda) : lambda => 
      if n < 0 {assert false}
      else {
        switch n {
        | 0 => churchNumB 
        | _ => helper(n-1, App(succ, churchNumB))
        }
      }
    helper(n, zero)
  }

  let test = () => {
    Js.log(print_lambda(eval(Let(pred,App(Var(0),toChurchNumB(8))))))
  }
}

let _ = DebruLetTest.test()