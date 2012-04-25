open Dot
open Toredex

let ex1 = [[ :concrete:
val z0 = new Top { z =>
                   L_a : Bottom .. Top { z =>
                                         L1_a: Bottom .. Top,
                                         L2_a: Bottom .. z.L1_a
                                     }
                 }
             {};
(app (fun (x: Top { z =>
                    L_a : Bottom .. Top { z =>
                                          L1_a: Bottom .. Top,
                                          L2_a: Bottom .. Top
                                        }
                  }) Top
           val z = new Top { z => l_v : Bottom -> Top }
                   {l_v(y : x.L_a /\ Top { z =>
                                           L1_a: Bottom .. z.L2_a,
                                           L2_a: Bottom .. Top
                                         }
                     ) = (fun (x0: y.L1_a) Top x0)};
		   (cast Top z))
     z0)
]]

let ex2 = [[ :concrete:
val x0 = new Top { z =>
                   L1_a : Bottom .. Top { z =>
                                          L2_a : Bottom .. Top,
                                          L3_a : Bottom .. Top,
                                          C2_c : Bottom .. z.L2_a
                                         }
                 }{};
val x1 = new Top { z =>
                   C1_c : Bottom .. Top { z => L1_a : Bottom .. x0.L1_a }
                 }{};
val x2 = new x1.C1_c { z =>
                       L1_a : Bottom .. x0.L1_a { z => L2_a : Bottom .. z.L3_a }
                      }{};
val x3 = new x1.C1_c { z =>
                       L1_a : Bottom .. x0.L1_a { z => L3_a : Bottom .. z.L2_a }
                      }{};
(app (fun (x: x1.C1_c) Top
          (fun (z0: x.L1_a /\ x3.L1_a) Top
               val z = new z0.C2_c {}; cast Top z
          )
     ) x2)
]]

let ex3 = [[ :concrete:
val z0 = new Top { z =>
                   L_a : Bottom .. Top { z =>
                                         L1_a: Bottom .. Top,
                                         L2_a: z.L1_a .. Top
                                     }
                 }
             {};
(app (fun (x: Top { z =>
                    L_a : Bottom .. Top { z =>
                                          L1_a: Bottom .. Top,
                                          L2_a: Bottom .. Top
                                        }
                  }) Top
           val z = new Top { z => l_v : Bottom -> Top }
                   {l_v(y : x.L_a /\ Top { z =>
                                           L1_a: z.L2_a .. Top,
                                           L2_a: Bottom .. Top
                                         }
                     ) = (fun (x0: y.L1_a) Top x0)};
		   (cast Top z))
     z0)
]]

let _ =
  print_string(toredex_preservation(ex1));
  print_string(toredex_preservation(ex2));
  print_string(toredex_preservation(ex3));
