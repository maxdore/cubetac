(TeX-add-style-hook
 "description"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("article" "11pt")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("algpseudocodex" "noEnd=True" "indLines=True")))
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "url")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "nolinkurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperbaseurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperimage")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperref")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "href")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "path")
   (TeX-run-style-hooks
    "latex2e"
    "algorithms"
    "article"
    "art11"
    "hyperref"
    "amsmath"
    "amssymb"
    "amsthm"
    "algorithm"
    "algpseudocodex"
    "ifthen"
    "tcolorbox")
   (TeX-add-symbols
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
    '("problem" 1)
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
    "exp:int"
    "exp:sndsphere"
    "exp:triangle"
    "alg:normalize"
    "alg:simple"
    "alg:subst2tele"
    "alg:teletosubst")
   (LaTeX-add-environments
    '("examplecontd" 1))
   (LaTeX-add-amsthm-newtheorems
    "definition"
    "theorem"
    "example"
    "expcont"))
 :latex)

