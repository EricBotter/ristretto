extern void println(int[] s);
extern int[] float2str(float n);

float add (float a, float b) {
    float c = a + b;
    return c;
}

void main() {
    float a = 5.3;
    float b = 6.2;
    int[] x = {0, 1, 2};
    int l = {0}.length;
    l = x.length;
    float c = add(a, b);
    println(float2str(c/5));
    return;
}