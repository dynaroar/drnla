## Framac slicing commands

```
frama-c bresenham1-invalid.c -slice-calls print -then-on 'Slicing export' -print
```
For example, static slicer in Frama-C uses abstract interpretaion to approximate program excution, however, this technique faces challenges when there is a complex NLA
expression in the program. In one example (bresenham1), the code fragment with polynomial expression is infesible to the target slcing location, Frama-C keeps this fragment due to its inability to approximate the program path. Applying our rewriting approach, the polynomial expression is replaced with its linear equivalent, Frama-C can successfully remove this code fragment, having a leaner slicing result.
   



