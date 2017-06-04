extern void println(int[] s);
extern int[] int2str(int n);
extern int[] float2str(float n);


float add (int a, float b) {
    float c = a + b;
    return c;
}

void main() {
    int a = 50;
    float b = 0.0;
    float[] x = {0.3, 1.0, 2.4, 2.4, 0.0, 1.3};

    int i = 0;
    while (i < x.length) {
		if (i % 2 == 0)
	    	b = b + x[i];
		else
	    	b = b - x[i];
    	i = i + 1;
    }
    float c = add(a, b);
    println(float2str(c));
    println(float2str(2 * 3.5 / 7));
	float y = 4 / 7.0;
	println(float2str(y));
    return;
}

/*/

int add (int a, int b) {
    int c = a + b;
    return c;
}

void main() {
    int a = 5;
    int b = 6;
    int[] x = {0, 1, 2};
    int l = {0}.length;
    l = x.length;
    int c = add(a, b);
    println(int2str(c/5));
    return;
}
*/