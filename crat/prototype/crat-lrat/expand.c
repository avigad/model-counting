#include <stdio.h>
#include <stdlib.h>

int main (int argc, char** argv) {
  FILE* input;

  int line[100000];

  input = fopen (argv[1], "r");

  int last = -1;
  int size = 0;
  for (;;) {
    int lit;
    int tmp = fscanf (input, " %i ", &lit);
    if (tmp == EOF) break;

    if (lit) line[size++] = lit;
    if (lit == 0) {
      if (line[0] == last + 2) {
        last++;
        printf ("%i %i %i 0\n", -last, last-2, last-1);
        printf ("%i %i 0\n", last, -last+2);
        printf ("%i %i 0\n", last, -last+1);
      }
      printf ("%i ", line[0]);
      for (int i = 1; i < size; i++)
        printf ("%i ", -line[i]);
      printf ("0\n");
      for (int i = 1; i < size; i++)
        printf ("%i %i 0\n", -line[0], line[i]);
      size = 0;
      last = line[0];
    }
  }

  last++;
  printf ("%i %i %i 0\n", -last, last-2, last-1);
  printf ("%i %i 0\n", last, -last+2);
  printf ("%i %i 0\n", last, -last+1);

}
