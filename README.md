# Dynamic Proofs of LTL

```
sudo cpan -i Time::Out
sudo cpan -i YAML::Tiny
```

### Installation

 * Install Ultimate to `/tools/ultimate`
 * Install DIG to `/tools/dig`
 * copy `scripts/*` to `/usr/local/bin` (or somewhere in your PATH)

### Usage


```
  $ dynamltl.py <filename> 
```

### Benchmarks

1. Execute the benchmarks:
```
DYNAMITE_HOME=/tools/ DYNAMITE_DEPS=/tools/ ./run nla-term run ultimate
# results will be saved in <tmpfolder>
```
2. Collect the results:
```
./harvest nocsvs nla-term <tmpfolder>
```