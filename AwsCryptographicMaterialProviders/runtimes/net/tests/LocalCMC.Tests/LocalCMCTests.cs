using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Text;
using AWS.Cryptography.KeyStore;
using AWS.Cryptography.MaterialProviders;
using Org.BouncyCastle.Security;
using Random_Compile;
using Xunit;


public class LocalCMCTests
{
  private static MaterialProviders mpl = new MaterialProviders(new MaterialProvidersConfig());
  private static ICryptographicMaterialsCache test = mpl.CreateCryptographicMaterialsCache(
      new CreateCryptographicMaterialsCacheInput { Cache = new CacheType{Default = new DefaultCache{EntryCapacity = 10}}}
    );
  
  private static ReadOnlyCollection<string> identifiers = 
    new ReadOnlyCollection<string>(new List<string>{
      "one",
      "two",
      "three",
      "four",
      "five",
      "six",
      "seven",
      "eight",
      "nine",
      "ten",
      "eleven",
      "twelve",
      "thirteen",
      "fourteen",
      "fifteen",
      "sixteen",
      "seventeen",
      "eighteen",
      "nineteen",
      "twenty",
      "twenty one"}
    );

  private static int ID_SIZE = identifiers.Count;

  [Fact]
  public void TestLotsOfAdding()
  {
    int threadCount = 10;
    int numTasks = 300000;
    
    ThreadPool.SetMaxThreads(threadCount, threadCount);
    for (int i = 0; i < numTasks; i++)
    {
      ThreadPool.QueueUserWorkItem(WorkForThread);
    }
  }

  private static void WorkForThread(object? state)
  {
    Console.WriteLine("TestLotsOfAdd");
    Random random = ThreadSafeRandom.getSecureRandom();
    var beaconKeyIdentifier = identifiers[random.Next(ID_SIZE)];

    MemoryStream cacheIdentifier = new MemoryStream(Encoding.UTF8.GetBytes(beaconKeyIdentifier));
    GetCacheEntryInput cacheEntryInput = new GetCacheEntryInput{Identifier = cacheIdentifier};

    try
    {
      GetCacheEntryOutput cacheEntryOutput = test.GetCacheEntry(cacheEntryInput);
    }
    catch (EntryDoesNotExist e)
    {
      Materials materials = new Materials
      {
        BeaconKey = new BeaconKeyMaterials
        {
          BeaconKeyIdentifier = beaconKeyIdentifier,
          BeaconKey = cacheIdentifier,
          EncryptionContext = new Dictionary<string, string>()
        }
      };

      PutCacheEntryInput putCacheEntryInput = new PutCacheEntryInput
      {
        Identifier = cacheIdentifier,
        CreationTime = DateTimeOffset.UnixEpoch.Second,
        ExpiryTime = DateTimeOffset.UnixEpoch.Second + 1,
        Materials = materials
      };

      test.PutCacheEntry(putCacheEntryInput);
    }
  }
  
  // ONLY USED FOR TESTING
  public partial class ThreadSafeRandom
  {
      [ThreadStatic] private static SecureRandom? _local;

      private static SecureRandom Instance
      {
          get
          {
              if (_local is null)
              {
                  _local = new SecureRandom();
              }
              return _local;
          }
      }

      public static SecureRandom getSecureRandom()
      {
          return Instance;
      }
  }

}
