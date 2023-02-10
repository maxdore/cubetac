(TeX-add-style-hook
 "description"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("algpseudocodex" "noEnd=True" "indLines=True")))
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "href")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperref")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperimage")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperbaseurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "nolinkurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "url")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "path")
   (TeX-run-style-hooks
    "latex2e"
    "algorithms"
    "llncs"
    "llncs10"
    "hyperref"
    "amsmath"
    "amssymb"
    "algorithm"
    "algpseudocodex"
    "ifthen"
    "tcolorbox")
   (TeX-add-symbols
    '("hcompcube" 9)
    '("filledsquare" 5)
    '("dimsquare" 2)
    '("dimcube" 3)
    '("substfour" 4)
    '("substtwo" 2)
    '("comp" 2)
    '("boundary" 1)
    '("cset" 1)
    '("pow" 1)
    '("cont" 2)
    '("dmap" 2)
    '("smap" 1)
    '("ctxtdim" 1)
    '("psh" 1)
    '("image" 1)
    '("restrict" 2)
    '("pintrestr" 3)
    '("pint" 1)
    '("mlist" 1)
    '("myproblem" 1)
    '("mname" 1)
    '("todo" 1)
    "continuation"
    "mdef"
    "join"
    "meet"
    "dedekind"
    "izero"
    "ione"
    "ivar"
    "oneconst"
    "oneid"
    "exampleautorefname"
    "algorithmautorefname"
    "arraystretch")
   (LaTeX-add-labels
    "sec:normalforms"
    "ssec:cubicalsets"
    "exp:int"
    "exp:sndsphere"
    "exp:triangle"
    "ssec:hits"
    "ssec:normalforms"
    "alg:normalize"
    "sec:contortionsolver"
    "ssec:cubicalcell"
    "ssec:ppm"
    "ssec:contortionsolver"
    "alg:simple"
    "sec:compositionsolver"
    "ssec:kanundecidable"
    "sec:cubicalagda"
    "alg:subst2tele"
    "alg:teletosubst"
    "ssec:inverses"
    "sec:conclusions")
   (LaTeX-add-environments
    '("proof" LaTeX-env-args ["argument"] 0)
    '("examplecontd" 1))
   (LaTeX-add-bibliographies
    "bibliography")
   (LaTeX-add-amsthm-newtheorems
    "expcont"))
 :latex)

