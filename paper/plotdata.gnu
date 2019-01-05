set terminal png
set style line 1 lc rgb "red"
set boxwidth 0.5
set style fill solid
set logscale y 10
unset label
set xlabel "Number of votes"
set ylabel "Time in Minutes"
plot "Experiment.dat" using 1:3:xtic(2) with boxes notitle linecolor rgb "#000000"
