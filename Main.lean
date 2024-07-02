import Manual
import Manual.Meta
import Verso.Genre.Manual

open Verso.Genre.Manual


def main :=
  manualMain (%doc Manual)
    (config := config)
where
  config := {
    extraFiles := [("static", "static")],
    extraCss := ["/static/theme.css", "/static/inter/inter.css", "/static/firacode/fira_code.css"]
  }
