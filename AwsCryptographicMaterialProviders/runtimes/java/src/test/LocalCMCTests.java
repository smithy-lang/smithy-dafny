import Random_Compile.ExternRandom;
import java.nio.ByteBuffer;
import java.nio.charset.StandardCharsets;
import java.time.Instant;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Random;
import org.testng.annotations.Test;
import software.amazon.cryptography.keystore.model.BeaconKeyMaterials;
import software.amazon.cryptography.materialproviders.ICryptographicMaterialsCache;
import software.amazon.cryptography.materialproviders.MaterialProviders;
import software.amazon.cryptography.materialproviders.model.CacheType;
import software.amazon.cryptography.materialproviders.model.CreateCryptographicMaterialsCacheInput;
import software.amazon.cryptography.materialproviders.model.DefaultCache;
import software.amazon.cryptography.materialproviders.model.EntryDoesNotExist;
import software.amazon.cryptography.materialproviders.model.GetCacheEntryInput;
import software.amazon.cryptography.materialproviders.model.GetCacheEntryOutput;
import software.amazon.cryptography.materialproviders.model.MaterialProvidersConfig;
import software.amazon.cryptography.materialproviders.model.Materials;
import software.amazon.cryptography.materialproviders.model.PutCacheEntryInput;

public class LocalCMCTests {

  private static final ICryptographicMaterialsCache test = MaterialProviders
    .builder()
    .MaterialProvidersConfig(MaterialProvidersConfig.builder().build())
    .build()
    .CreateCryptographicMaterialsCache(
      CreateCryptographicMaterialsCacheInput
        .builder()
        .cache(
          CacheType
            .builder()
            .Default(DefaultCache.builder().entryCapacity(10).build())
            .build()
        )
        .build()
    );
  private static final List<String> identifies = Collections.unmodifiableList(
    Arrays.asList(
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
    )
  );
  private static final int IDS_SIZE = identifies.size();

  @Test(threadPoolSize = 10, invocationCount = 300000, timeOut = 10000)
  public void TestALotOfAdding() {
    Random rand = ExternRandom.getSecureRandom();
    String beaconKeyIdentifier = identifies.get(rand.nextInt(IDS_SIZE));

    ByteBuffer cacheIdentifier = ByteBuffer.wrap(
      beaconKeyIdentifier.getBytes(StandardCharsets.UTF_8)
    );

    GetCacheEntryInput getCacheEntryInput = GetCacheEntryInput
      .builder()
      .identifier(cacheIdentifier)
      .build();

    try {
      GetCacheEntryOutput getCacheEntryOutput = test.GetCacheEntry(
        getCacheEntryInput
      );
      //      assertEquals(getCacheEntryOutput.materials().BeaconKey().beaconKey(), binaryData);
      //      assertEquals(getCacheEntryOutput.materials().BeaconKey().beaconKeyIdentifier(),
      // stringData);
      //      System.out.println("are equal");
    } catch (EntryDoesNotExist ex) {
      Materials materials = Materials
        .builder()
        .BeaconKey(
          BeaconKeyMaterials
            .builder()
            .beaconKeyIdentifier(beaconKeyIdentifier)
            // The cacheIdentifier is used as the material
            // because we are not testing the cryptography here.
            .beaconKey(cacheIdentifier)
            .encryptionContext(new HashMap<String, String>())
            .build()
        )
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
