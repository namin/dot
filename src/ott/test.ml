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

let _ =
  print_string(toredex_preservation(ex1));
