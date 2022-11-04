(TeX-add-style-hook
 "algpseudocodex"
 (lambda ()
   (TeX-run-style-hooks
    "kvoptions"
    "algorithmicx"
    "etoolbox"
    "fifo-stack"
    "varwidth"
    "tabto"
    "tikz")
   (TeX-add-symbols
    '("BoxedString" ["argument"] 1)
    '("BeginBox" ["argument"] 0)
    "algpx"
    "EndBox")
   (LaTeX-add-lengths
    "algpx")
   (LaTeX-add-saveboxes
    "algpx"))
 :latex)

