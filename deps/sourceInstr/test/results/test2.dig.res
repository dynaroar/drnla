data.traces:WARNING:trace x=0,y=-260,atomic0=0 exist
data.traces:WARNING:trace x=0,y=-4,atomic0=0 exist
data.traces:WARNING:trace x=0,y=-16,atomic0=0 exist
data.traces:WARNING:trace x=0,y=-282,atomic0=0 exist
* prog test2 locs 2;  invs 13 (Eqt: 3, MMP: 4, Oct: 6) V 3 T 2 D 1;  NL 0 (1) ;
-> time eqts 3.6s, ieqs 0.5s, minmax 0.8s, simplify 0.5s, symbolic_states 25.1s, total 31.2s
-> checks  0 () change depths 0 () change vals 0 ()
-> max  0 () change depths 0 ()
runs 1
rand seed 1628048678.87, test (42, 98)
vtrace1 (7 invs):
1. atomic0 == 0
2. -atomic0 <= 0
3. atomic0 - x <= -2
4. -atomic0 - y <= -1
5. atomic0 - min(y, 0) == 0
6. min(x, 0) - atomic0 == 0
7. min(x, y, 0) - atomic0 == 0
vtrace2 (6 invs):
1. x == 0
2. atomic0 == 0
3. x <= 0
4. y <= -1
5. atomic0 - x <= 0
6. atomic0 - max(y, 0) == 0
tmpdir: /var/tmp/dig_2006083155761171750_m7vqu1qq
