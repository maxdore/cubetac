(TeX-add-style-hook
 "description"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("article" "11pt")))
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
    "article"
    "art11"
    "hyperref"
    "amsmath"
    "amssymb"
    "amsthm"
    "algorithm"
    "algpseudocodex")
   (TeX-add-symbols
    '("substfour" 4)
    '("substtwo" 2)
    '("boundary" 1)
    '("cset" 1)
    '("pow" 1)
    '("deg" 1)
    '("dmap" 2)
    '("smap" 1)
    '("ctxtdim" 1)
    '("dim" 1)
    '("hom" 2)
    '("psh" 1)
    '("pint" 1)
    '("problem" 1)
    '("mname" 1)
    "continuation"
    "mdef"
    "join"
    "meet"
    "dedekind"
    "constzero"
    "exampleautorefname"
    "arraystretch")
   (LaTeX-add-labels
    "exp:int"
    "exp:loopspace"
    "exp:triangle"
    "exp:assoc"
    "exp:group"
    "alg:boundary"
    "alg:normalize"
    "alg:wellformedboundary"
    "alg:wellformedcontext"
    "alg:simple"
    "alg:subst2tele"
    "alg:teletosubst")
   (LaTeX-add-environments
    '("examplecontd" 1))
   (LaTeX-add-amsthm-newtheorems
    "definition"
    "example"
    "expcont"))
 :latex)

