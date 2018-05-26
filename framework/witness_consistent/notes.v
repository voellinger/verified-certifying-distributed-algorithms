Terminierung
  - wie kann man einen terminierungs-zustand beschreiben?
  
  - was sind m\u00f6gliche algorithmische eintrittsm\u00f6glichkeiten
- invarianten
- mit verdi rumexperimentieren f\u00fcr hauptbeweis



fj Knoten k:
  terminated := false
  consistent := true
  kinderliste := alle kinder von k
  Var_list := Var_list //liste von eigener Variablenbelegung

  InputHandler ()
  - wenn kinderliste leer:
    - sende Var_list an parent(k)(<> k)
    - terminated := true

  NetHandler(sender, vlist)
    - fj (Variable, Belegung) aus vlist:
      - Variable schon in Var_list?
        ja: Belegung = Var_list(Variable)?
          nein: consistent := false
        nein: Var_list :+= (Variable, Belegung)
    - entferne sender aus kinderliste
    - wenn kinderliste leer:
      - sende Var_list an parent(k)(<> k)
      - terminated := true


auf effizienz modifizierbar, 
  indem jeder normale knoten die belegungspr\u00fcfung macht und dann 
    nur noch FALSE weiterreicht 
    oder nur noch eine belegung jeder variablen weiterreicht
jeder Knoten muss dann zus\u00e4tzlich noch FALSE von den kindern mit einberechnen