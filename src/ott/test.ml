open Dot
open Toredex

let ex1 = [[ :concrete:
  val v = new Top { z =>
                    L_a : Bottom .. Top,
                    l_v : Top { z => L_a : Bottom .. Top }
                  }{l_v = v : Top { z => L_a : Bottom .. Top }};
  (app (fun (x: Top) Top x)
       ((v : Top { z => l_v : Top }).l_v))
]]

let ex2 = [[ :concrete:
  val v = new Top { z =>
                    A_a : Top .. Top,
                    B_a : Bottom .. Top,
                    m_m : Top { z => A_a : Top .. Top } -> Top { z => A_a : Top .. Top }
                   }{m_m(x)=x};
  (app (fun (x: Top) Top x)
       ((v : Top { z => m_m : Top { z =>
                                    A_a : Top .. Top,
                                    B_a : Bottom .. Top
                                   }
                              ->
                              Top })
        m_m
        (v : Top { z =>
                   A_a : Top .. Top,
                   B_a : Bottom .. Top
                 })))
]]

let _ =
  print_string(toredex_preservation(ex1));
  print_string(toredex_preservation(ex2));
