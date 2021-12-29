#include <stdio.h>
#include <string.h>
#include <assert.h>

struct Test
{
  int field1;
  int field2;
};

int ML_Test_get_field1 (struct Test * t) { return t->field1; }
void ML_Test_set_field1 (struct Test * t, int v) { t->field1 = v; }

int ML_Test_get_field2 (struct Test * t) { return t->field2; }
void ML_Test_set_field2 (struct Test * t, int v) { t->field2 = v; }

/*
void * Test_getField (struct Test * t, char * fname)
{
    if (!strcmp(fname, "field1")) return t->field1;
    else if (!strcmp(fname, "field2")) return t->field2;
    else assert(0);
}

// must pass by pointer to actually make change!
void Test_setField (struct Test * t, char * fname, void * v)
{
    if (!strcmp(fname, "field1")) t->field1 = (int)v;
    else if (!strcmp(fname, "field2")) t->field2 = (int)v;
    else assert(0);
}
*/

// test case that uses structs in the source but not in the target
int test (int f1, int f2)
{

    struct Test t;
    //t.field1 = f1;
    //Test_setField(&t, "field1", f1);
    ML_Test_set_field1(&t, f1);

    //t.field2 = f2;
    //Test_setField(&t, "field2", f2);
    ML_Test_set_field2(&t, f2);

    //return t.field1 + t.field2;
    //return (int)Test_getField(&t, "field1") + (int)Test_getField(&t, "field2");
    return ML_Test_get_field1(&t) + ML_Test_get_field2(&t);

}

int main (int argc, char ** argv)
{
    printf("%d\n", test(2, 20));
    return 0;
}