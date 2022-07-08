# DrNLA Artifact Check list

 
### Benckmarks

- ctl-svcomp: nla version, T2 versions, and FuncTion versions.
- ctl-pldi13-nla: nla version, T2 versions, and FuncTion versions.
- ctl-pldi13-nlas: various type of nlas, T2 versions, and FuncTion versions.
- ctl-multi: handcrafted nla benchmarks, T2 versions, and FuncTion versions.


### Source Code (main contribution)

- `drnla.py`: DrNLA driver.
- `analysis.py`: dual refinement algorithm.
- `dynamic.py`: dynamic learning.
- `static.py`: static validation.
- `solver.py`: smt solver, constraints solving related.
- `transform.py`: setup from c transformation.
- `ultils/*`: environment setting up and other utilities.

### Dependencies

- `dyn_instr source`: Ctransformation (main contribution).
- `dig`: dynamic learning engine. obtain [here](https://github.com/dynaroars/dig).
- `Ultimate-linux`: static validator, [here](https://github.com/ultimate-pa/ultimate).
