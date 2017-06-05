extern void println(int[] s);
extern int[] int2str(int n);
extern int[] float2str(float n);

float add (int a, float b) {
    float c = a + b;
    return c;
}

void main() {
    float[] x = {0.3, 1.0, 2.4, 2.4, 0.0, 1.3};

	// add odd-placed numbers, subtract even-placed numbers
    int i = 0;
    float sum = 0.0;
    while (i < x.length) {
		if (i % 2 == 0)
	    	sum = sum + x[i];
		else
	    	sum = sum - x[i];
    	i = i + 1;
    }
    println(float2str(sum));

	// compute average while it's less than 1
    float avg = x[0];
	i = 1;
    while (avg < i && i < x.length) {
    	avg = avg + x[i];
    	i = i + 1;
    }
    avg = avg / i;
	println(float2str(avg));

	// demonstrate calls
	println(float2str(add(6, 4.8));

	// more demos
	float y = 4 / 7.0;
	println(float2str(y));

    println(float2str(2 * 3.5 / 7));

    return;
}
