# Lean Language Reference

## Building the Reference Manual

To read the manual, run the following command:

```
lake exe generate-manual --depth 2
```

Then run a local web server on its output:
```
python3 -m http.server 8880 --directory _out/html-multi &
```

Then open <http://localhost:8880> in your browser.
