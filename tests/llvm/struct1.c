#include <stdio.h>
#include <string.h>
//#include <assert.h>

struct Test
{
  int field1;
  int field2;
};

// following code needs to be generated
// option 1: generate the following field specific set/getters
int ML_Test_get_field1 (struct Test * t) { return t->field1; }
void ML_Test_set_field1 (struct Test * t, int v) { t->field1 = v; }

int ML_Test_get_field2 (struct Test * t) { return t->field2; }
void ML_Test_set_field2 (struct Test * t, int v) { t->field2 = v; }

// option 2: generate generic set/getters for all classes. this compiles to ugly llvm code!
/*
void ML_setField(void * obj, char * tname, char * fname, void * v)
{
    if (!strcmp(tname, "Test"))
    {
        if (!strcmp(fname, "field1")) ((struct Test*)obj)->field1 = (int)v;
        else if (!strcmp(fname, "field2")) ((struct Test*)obj)->field2 = (int)v;
        else assert(0);
    }
    else assert(0);
}

void * ML_getField(void * obj, char * tname, char * fname)
{
    if (!strcmp(tname, "Test"))
    {
        if (!strcmp(fname, "field1")) return ((struct Test*)obj)->field1;
        else if (!strcmp(fname, "field2")) return ((struct Test*)obj)->field2;
        else assert(0);
    }
    else assert(0);
}
*/

// test case that uses structs in the source but not in the target
int test (int f1, int f2)
{

    struct Test t;
    //t.field1 = f1;
    //ML_setField(&t, "Test", "field1", f1);
    ML_Test_set_field1(&t, f1);

    //t.field2 = f2;
    //ML_setField(&t, "Test", "field2", f2);
    ML_Test_set_field2(&t, f2);

    //return t.field1 + t.field2;
    //return (int)ML_getField(&t, "Test", "field1") + (int)ML_getField(&t, "Test", "field2");
    return ML_Test_get_field1(&t) + ML_Test_get_field2(&t);

}

int main (int argc, char ** argv)
{
    printf("%d\n", test(5, 20));
    return 0;
}
