using System;
using _0_LinkedList_Compile;
 
public class UseLinkedList
{
    public static void Main()
    {
	Console.WriteLine("creating singleton list");
	var l1 = new Node<int>();
	l1.Singleton(3);
	Console.WriteLine("inserting into singleton list");
	var l2 = new Node<int>();
	l2.Insert(4, l1);
	Console.WriteLine(l2.next.elem);
    }
}
