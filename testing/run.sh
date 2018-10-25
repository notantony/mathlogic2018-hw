cat test.txt > input.txt
./3.exe;
cat input.txt | sed "s/=/-/g" > tmp.txt;
cat tmp.txt > input.txt;
echo '' >> input.txt;
cat output.txt >> input.txt;
./1.exe;
cat output.txt | grep "Не"