
int g(int x){
  return x;
}

int f(int a, int b){
  b = g(8);
  print(a);
  print(b);
  return 0;
}

int main(int argc, char* argv[]){
  f(3,4);
  return 0;
}
