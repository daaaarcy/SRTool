void main() {
int i;
int iterations;
i=0;
// make iterations positive, but otherwise unconstrained
assume(iterations > 0);
// define two invariants
while(i < iterations)
inv(i <= iterations)
inv(i >= 0)
{
i = i + 1;
}
assert(i == iterations);
}
