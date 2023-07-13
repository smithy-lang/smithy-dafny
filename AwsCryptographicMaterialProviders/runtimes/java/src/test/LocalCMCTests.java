

import org.testng.annotations.BeforeClass;
import org.testng.annotations.Test;
import software.amazon.cryptography.keystore.model.BeaconKeyMaterials;
import software.amazon.cryptography.materialproviders.ICryptographicMaterialsCache;
import software.amazon.cryptography.materialproviders.MaterialProviders;
import software.amazon.cryptography.materialproviders.model.*;

import java.nio.ByteBuffer;
import java.nio.charset.StandardCharsets;
import java.time.Instant;
import java.util.Arrays;
import java.util.List;
import java.util.Random;

import static org.testng.Assert.assertEquals;


public class LocalCMCTests {

  static private ICryptographicMaterialsCache test = MaterialProviders
    .builder()
    .MaterialProvidersConfig(MaterialProvidersConfig.builder().build())
    .build()
    .CreateCryptographicMaterialsCache(CreateCryptographicMaterialsCacheInput
      .builder()
      .cache(CacheType.builder().defaultCache(DefaultCache.builder().entryCapacity(10).build()).build())
      .build()
    );
  static private List<String> identifies = Arrays.asList(
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
    "twenty one"
  );
  static private Random rand = new Random();


  @Test(threadPoolSize = 10, invocationCount = 300000, timeOut = 10000)
  public void TestALotOfAdding() {
    String beaconKeyIdentifier = identifies.get(rand.nextInt(identifies.size()));

    ByteBuffer cacheIdentifier = ByteBuffer.wrap(beaconKeyIdentifier.getBytes(StandardCharsets.UTF_8));

    GetCacheEntryInput getCacheEntryInput = GetCacheEntryInput
      .builder()
      .identifier(cacheIdentifier)
      .build();

    try {
      GetCacheEntryOutput getCacheEntryOutput = test.GetCacheEntry(getCacheEntryInput);
//      assertEquals(getCacheEntryOutput.materials().BeaconKey().beaconKey(), binaryData);
//      assertEquals(getCacheEntryOutput.materials().BeaconKey().beaconKeyIdentifier(), stringData);
//      System.out.println("are equal");
    } catch (EntryDoesNotExist ex) {
      Materials materials = Materials
        .builder()
        .BeaconKey(BeaconKeyMaterials
          .builder()
          .beaconKeyIdentifier(beaconKeyIdentifier)
          // The cacheIdentifier is used as the material
          // because we are not testing the cryptography here.
          .beaconKey(cacheIdentifier)
          .build())
        .build();

      PutCacheEntryInput putCacheEntryInput = PutCacheEntryInput
        .builder()
        .identifier(cacheIdentifier)
        .creationTime(Instant.now().getEpochSecond())
        .expiryTime(Instant.now().getEpochSecond() + 1)
        .materials(materials)
        .build();
        test.PutCacheEntry(putCacheEntryInput);
    }

  }


}
