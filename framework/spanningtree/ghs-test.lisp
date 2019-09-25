








(setq g ''(((a . b). 3) ((a . d). 1) ((b . e). 2) ((c . d). 5) ((a . C). 4) ((e . C). 6) ((f . d) 8) ((f . a) 9) ) )
(do ((state (nqthm-eval `(ghs0 0 nil ,g) :untranslate T) (nqthm-eval `(ghs 1 nil ,g ,state) :untranslate T))
     (red 1 (nqthm-eval `(myghs1 ,state) :untranslate T))
    )
    ((and (listp red) (equal T (nqthm-eval `(get-terminated ,red) :untranslate T))) (nqthm-eval `(get-rest ,red) :untranslate T))())


