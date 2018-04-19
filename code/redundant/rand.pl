#!/usr/bin/perl

sub rand_pref {
  return 1 + int (rand (4));
}

$n = $ARGV[0];
for ($i = 0; $i < $n; $i++) {
  print "(A, "; print rand_pref; print "); ";
  print "(B, "; print rand_pref; print "); ";
  print "(C, "; print rand_pref; print "); ";
  print "(D, "; print rand_pref; print "); ";
  print "(E, "; print rand_pref; print "); ";
  print "(F, "; print rand_pref; print "); ";
  print "(G, "; print rand_pref; print "); ";
  print "(H, "; print rand_pref; print "); ";
  print "(I, "; print rand_pref; print "); ";
  print "(J, "; print rand_pref; print "); ";
  print "(K, "; print rand_pref; print "); ";
  print "(L, "; print rand_pref; print "); ";
  print "(N, "; print rand_pref; print "); ";
  print "(P, "; print rand_pref; print "); ";
  print "(Q, "; print rand_pref; print "); ";
  print "(R, "; print rand_pref; print "); ";
  print "(T, "; print rand_pref; print "); ";
  print "(U, "; print rand_pref; print "); ";
  print "(V, "; print rand_pref; print "); ";
  print "(X, "; print rand_pref; print ")\n";
  #print "(Y, "; print rand_pref; print "); ";
  #print "(Z, "; print rand_pref; print ")\n";
	
}
