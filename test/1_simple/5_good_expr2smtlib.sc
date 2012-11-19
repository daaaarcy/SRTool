
void main(int i, int j)
{
	i=1+9;
	j=2+8;

	assert(i > j);
	assert(i < j);
	assert(i >= j);
	assert(i <= j);
	assert(i / j != 1);
	assert(i * j == 100);
    assert((i ^ j) == 1);
    assert((i + j) == 1);
    assert((i && j) == 1);
    assert((i || j) == 1);
    assert((i & j) == 1);
    assert((i | j) == 1);
    assert((i << 2) == 1);
    assert((i >> 2) == 1);
    assert((i % 2) == 1);
}
