package software.amazon.polymorph.utils;

import java.util.HashMap;
import java.util.Map;

public final class MapUtils {

  /**
   * Returns a new map containing every key that appears in any of the given maps,
   * associated with its value in the last given map where the key appears.
   */
  @SafeVarargs
  public static <K, V> Map<K, V> merge(Map<K, V>... maps) {
    final Map<K, V> result = new HashMap<>();
    for (final Map<K, V> map : maps) {
      result.putAll(map);
    }
    return result;
  }
}
