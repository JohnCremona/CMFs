// usage: magma -b N_min:={} N_max:={} aldims_weight_2.m
// This is for N <= 50000, k = 2
import "magma/aldims.m" : write_ALdims_upto;

write_ALdims_upto(eval(N_min), eval(N_max), 2);

exit;