// usage: magma -b Nk2_min:={} Nk2_max:={} aldims_run_Nk2.m
// This is for Nk^2 <= 40000
import "magma/aldims.m" : write_ALdims_Nk2_upto;

write_ALdims_Nk2_upto(eval(Nk2_min), eval(Nk2_max));

exit;