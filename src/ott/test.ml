open Dot
open Toredex

let x = "x"
let x0 = "x0"
let x1 = "x1"
let x2 = "x2"
let x3 = "x3"

let y = "y"

let z0 = "z0"
let z = "z"

let tLa1 = Tlabel_abstract "La1"
let tLa2 = Tlabel_abstract "La2"
let tLa3 = Tlabel_abstract "La3"

let tLc1 = Tlabel_class "Lc1"
let tLc2 = Tlabel_class "Lc2"

let tL = Tlabel_abstract "L"

let l = Vlabel_any"l"

let ex1 = [[
val z0 = new Top { z =>
                   L : Bottom .. Top { z =>
                                       La1: Bottom .. Top,
                                       La2: Bottom .. z.La1
                                     }
                 }
             {};
(app (fun (x: Top { z =>
                    L : Bottom .. Top { z =>
                                        La1: Bottom .. Top,
                                        La2: Bottom .. Top
                                      }
                  }) Top
           val z = new Top { z => l : Bottom -> Top }
                   {l(y : x.L /\ Top { z =>
                                       La1: Bottom .. z.La2,
                                       La2: Bottom .. Top
                                     }
                     ) = (fun (x0: y.La1) Top x0)};
		   (cast Top z))
     z0)
]]

let ex2 = [[
val x0 = new Top { z =>
                   La1 : Bottom .. Top { z =>
                                         La2 : Bottom .. Top,
                                         La3 : Bottom .. Top,
                                         Lc2 : Bottom .. z.La2
                                       }
                 }{};
val x1 = new Top { z =>
                   Lc1 : Bottom .. Top { z => La1 : Bottom .. x0.La1 }
                 }{};
val x2 = new x1.Lc1 { z =>
                      La1 : Bottom .. x0.La1 { z => La2 : Bottom .. z.La3 }
                    }{};
val x3 = new x1.Lc1 { z =>
                      La1 : Bottom .. x0.La1 { z => La3 : Bottom .. z.La2 }
                    }{};
(app (fun (x: x1.Lc1) Top
          (fun (z0: x.La1 /\ x3.La1) Top
               val z = new z0.Lc2 {}; cast Top z
          )
     ) x2)
]]

let _ =
  print_string(toredex_preservation(ex1));
  print_string(toredex_preservation(ex2));
