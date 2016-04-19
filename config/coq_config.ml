(* DO NOT EDIT THIS FILE: automatically generated by ../configure *)

let local = false
let coqrunbyteflags = "-dllib -lcoqrun -dllpath '/usr/local/coq-versions/8.4.timings/lib/coq'"
let coqlib = Some "/usr/local/coq-versions/8.4.timings/lib/coq"
let configdir = None
let datadir = None
let docdir = "/usr/local/coq-versions/8.4.timings/share/doc/coq"
let ocaml = "ocaml"
let ocamlc = "ocamlc"
let ocamlopt = "ocamlopt"
let ocamlmklib = "ocamlmklib"
let ocamldep = "ocamldep"
let ocamldoc = "ocamldoc"
let ocamlyacc = "ocamlyacc"
let ocamllex = "ocamllex"
let camlbin = "/usr/bin"
let camllib = "/usr/lib/ocaml"
let camlp4 = "camlp5"
let camlp4o = "camlp5o"
let camlp4bin = "/usr/bin"
let camlp4lib = "/usr/lib/ocaml/camlp5"
let camlp4compat = "-loc loc"
let coqideincl = "-I /usr/lib/ocaml/lablgtk2"
let cflags = "-Wall -Wno-unused"
let best = "opt"
let arch = "Linux"
let has_coqide = "opt"
let gtk_platform = `X11
let has_natdynlink = true
let natdynlinkflag = "true"
let osdeplibs = "-cclib -lunix"
let version = "8.4pl6"
let caml_version = "4.01.0"
let date = "April 2016"
let compile_date = "Apr 06 2016 18:17:23"
let vo_magic_number = 08400
let state_magic_number = 58400
let exec_extension = ""
let with_geoproof = ref false
let browser = "firefox -remote \"OpenURL(%s,new-tab)\" || firefox %s &"
let wwwcoq = "http://coq.inria.fr/"
let wwwrefman = wwwcoq ^ "distrib/" ^ version ^ "/refman/"
let wwwstdlib = wwwcoq ^ "distrib/" ^ version ^ "/stdlib/"
let localwwwrefman = "file:/" ^ docdir ^ "html/refman"

let theories_dirs = [
"Arith";
"Bool";
"Classes";
"FSets";
"Init";
"Lists";
"Logic";
"MSets";
"NArith";
"Numbers";
"Numbers/Rational";
"Numbers/Rational/SpecViaQ";
"Numbers/Rational/BigQ";
"Numbers/NatInt";
"Numbers/Cyclic";
"Numbers/Cyclic/Int31";
"Numbers/Cyclic/ZModulo";
"Numbers/Cyclic/DoubleCyclic";
"Numbers/Cyclic/Abstract";
"Numbers/Integer";
"Numbers/Integer/BigZ";
"Numbers/Integer/NatPairs";
"Numbers/Integer/SpecViaZ";
"Numbers/Integer/Binary";
"Numbers/Integer/Abstract";
"Numbers/Natural";
"Numbers/Natural/BigN";
"Numbers/Natural/Peano";
"Numbers/Natural/SpecViaZ";
"Numbers/Natural/Binary";
"Numbers/Natural/Abstract";
"PArith";
"Program";
"QArith";
"Reals";
"Relations";
"Setoids";
"Sets";
"Sorting";
"Strings";
"Structures";
"Unicode";
"Vectors";
"Wellfounded";
"ZArith";
]
let plugins_dirs = [
"cc";
"decl_mode";
"extraction";
"field";
"firstorder";
"fourier";
"funind";
"micromega";
"nsatz";
"omega";
"quote";
"ring";
"romega";
"rtauto";
"setoid_ring";
"subtac";
"subtac/test";
"syntax";
"xml";
]