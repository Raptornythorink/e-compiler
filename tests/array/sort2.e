int main(int argc,char* argv[]){
  int a = atoi(argv[1]);
  int b = atoi(argv[2]);
  int t[10];
  t[0] = 5;
  t[1] = 7;
  t[2] = 3;
  t[3] = 8;
  t[4] = 12;
  t[5] = 1;
  t[6] = 4;
  t[7] = 7;
  t[8] = 2;
  t[9] = 9;
  sort(t,0,9);
  int i = 0;
  while(i < 10){
  print(5000);
    print(i);
    print(t[i]);
    i = i + 1;
  }
  return 0;
}
int sort(int* t, int begin, int end){
//  print(10000+100*begin+end);
  if (begin < end){
    int pivot = begin;
    pivot = partition(t, begin, end, pivot);
    sort(t, begin, pivot-1);
    sort(t, pivot+1, end);
  }
}
int swap(int* t, int i,int j){

  int tmp = t[i];
  t[i] = t[j];
  t[j] = tmp;
  return 0;
}
int partition(int* t, int begin, int end, int pivot){
  swap(t, pivot, end);
  int j = begin;
  int i = begin;
  while(i <= end - 1){
  //print(4000000+10000*i+end);

if(t[i] <= t[end]){
      swap(t, i, j);
      j = j + 1;
    }
    i = i + 1;
  }
  swap(t, end, j);
  return j;
}
