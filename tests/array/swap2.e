int main(int argc,char* argv[]){
  int t[10];
  t[0] = 5;
  t[1] = 12;
  partition(t,0,1,0);
  print(t[0]);
  print(t[1]);
  return 0;
}
int swap(int* t,int i,int j){
  int tmp = t[i];
  t[i] = t[j];
  t[j] = tmp;
  return 0;
}
int partition(int* t, int begin, int end, int pivot){

int tmp = t[pivot];
t[pivot] = t[end];
t[end] = tmp;
  int j = begin;
  int i = begin;
  while(i <= end - 1){
    if(t[i] <= t[end]){
tmp = t[i];
t[i] = t[j];
t[j] = tmp;

      j = j + 1;
    }
    i = i + 1;
  }

tmp = t[end];
t[end] = t[j];
t[j] = tmp;

  return j;
}

