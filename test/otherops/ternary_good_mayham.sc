
void main(int w)
{
    int x;
    int y;
    int z;
     
    if(10?11:0){
        z = 5;
        if(z==0){
           y = 4 + 2;
        }else{
            if(w){
                y = 14;
             }
             y=1;
             if(z?4:0){
                 x = y + z;
             }
        }
    }else{
        z = 3;
    }
    
    assert(z==5);
    assert(y==1);
    assert(x==(z+y));
}
