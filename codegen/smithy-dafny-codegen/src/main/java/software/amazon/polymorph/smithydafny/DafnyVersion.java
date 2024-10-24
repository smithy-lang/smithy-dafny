// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithydafny;

import java.util.Comparator;
import java.util.Objects;

/**
 * Representation of a Dafny version number, according to SemVer 1.0 semantics.
 *
 * Note that Dafny pre-releases historically have used pre-release suffixes slightly wrong:
 * after releasing 4.2 for example, the nightly pre-releases will have version numbers like
 * "4.2.0-nightly-2023-08-04-656a114", but that should actually be interpreted as a pre-release
 * for 4.2 rather than 4.3. So far that's immaterial for this code base,
 * but if it becomes relevant the better solution is for Dafny pre-releases to correct this instead.
 */
public class DafnyVersion implements Comparable<DafnyVersion> {

  private final int major;
  private final int minor;
  private final int patch;
  // Will be non-null only if there was a pre-release suffix
  private final String prerelease;
  // Will be non-null only if there was a build suffix
  private final String build;

  // Anything with a pre-release suffix should be considered less
  // than a matching version without one.
  private static final Comparator<String> SUFFIX_COMPARATOR =
    Comparator.nullsLast(Comparator.naturalOrder());

  public static DafnyVersion parse(String versionString) {
    if (!versionString.matches("[0-9.A-Za-z\\-+]*")) {
      throw new IllegalArgumentException();
    }
    String majorMinorPatch = versionString;
    String suffix = null;
    String build = null;

    int plusIndex = majorMinorPatch.indexOf("+");
    if (plusIndex >= 0) {
      build = majorMinorPatch.substring(plusIndex + 1);
      majorMinorPatch = versionString.substring(0, plusIndex);
    }

    int firstHyphenIndex = majorMinorPatch.indexOf("-");
    if (firstHyphenIndex >= 0) {
      suffix = majorMinorPatch.substring(firstHyphenIndex + 1);
      majorMinorPatch = majorMinorPatch.substring(0, firstHyphenIndex);
    }
    String[] splitByDots = majorMinorPatch.split("\\.");
    switch (splitByDots.length) {
      case 1:
        return new DafnyVersion(
          Integer.parseInt(splitByDots[0]),
          0,
          0,
          suffix,
          build
        );
      case 2:
        return new DafnyVersion(
          Integer.parseInt(splitByDots[0]),
          Integer.parseInt(splitByDots[1]),
          0,
          suffix,
          build
        );
      case 3:
        return new DafnyVersion(
          Integer.parseInt(splitByDots[0]),
          Integer.parseInt(splitByDots[1]),
          Integer.parseInt(splitByDots[2]),
          suffix,
          build
        );
      default:
        throw new IllegalArgumentException();
    }
  }

  public DafnyVersion(int major, int minor, int patch) {
    this(major, minor, patch, null);
  }

  public DafnyVersion(int major, int minor, int patch, String prerelease) {
    this(major, minor, patch, prerelease, null);
  }

  public DafnyVersion(
    int major,
    int minor,
    int patch,
    String prerelease,
    String build
  ) {
    this.major = requireNonNegative(major);
    this.minor = requireNonNegative(minor);
    this.patch = requireNonNegative(patch);
    this.prerelease = prerelease;
    this.build = build;
  }

  private int requireNonNegative(int value) {
    if (value < 0) {
      throw new IllegalArgumentException();
    }
    return value;
  }

  public int getMajor() {
    return major;
  }

  public int getMinor() {
    return minor;
  }

  public int getPatch() {
    return patch;
  }

  public String getPrerelease() {
    return prerelease;
  }

  public String getBuild() {
    return build;
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) {
      return true;
    }
    if (o == null || getClass() != o.getClass()) {
      return false;
    }
    DafnyVersion that = (DafnyVersion) o;
    return (
      major == that.major &&
      minor == that.minor &&
      patch == that.patch &&
      Objects.equals(prerelease, that.prerelease) &&
      Objects.equals(build, that.build)
    );
  }

  @Override
  public int hashCode() {
    return Objects.hash(major, minor, patch, prerelease, build);
  }

  @Override
  public int compareTo(DafnyVersion other) {
    int majorComparison = Integer.compare(this.major, other.major);
    if (majorComparison != 0) {
      return majorComparison;
    }

    int minorComparison = Integer.compare(this.minor, other.minor);
    if (minorComparison != 0) {
      return minorComparison;
    }

    int patchComparison = Integer.compare(this.patch, other.patch);
    if (patchComparison != 0) {
      return patchComparison;
    }

    return SUFFIX_COMPARATOR.compare(this.prerelease, other.prerelease);
  }

  public String unparse() {
    StringBuilder builder = new StringBuilder();
    builder.append(major);
    builder.append('.');
    builder.append(minor);
    builder.append('.');
    builder.append(patch);
    if (prerelease != null) {
      builder.append('-');
      builder.append(prerelease);
    }
    if (build != null) {
      builder.append('+');
      builder.append(build);
    }
    return builder.toString();
  }

  @Override
  public String toString() {
    return (
      "DafnyVersion{" +
      "major=" +
      major +
      ", minor=" +
      minor +
      ", patch=" +
      patch +
      ", prerelease='" +
      prerelease +
      '\'' +
      ", build='" +
      build +
      '\'' +
      '}'
    );
  }
}
