// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package simple.constraints.model;

import java.nio.ByteBuffer;
import java.util.List;
import java.util.Map;
import java.util.Objects;

public class GetConstraintsInput {
  private final String MyString;

  private final String NonEmptyString;

  private final String StringLessThanOrEqualToTen;

  private final ByteBuffer MyBlob;

  private final ByteBuffer NonEmptyBlob;

  private final ByteBuffer BlobLessThanOrEqualToTen;

  private final List<String> MyList;

  private final List<String> NonEmptyList;

  private final List<String> ListLessThanOrEqualToTen;

  private final Map<String, String> MyMap;

  private final Map<String, String> NonEmptyMap;

  private final Map<String, String> MapLessThanOrEqualToTen;

  private final String Alphabetic;

  private final int OneToTen;

  private final int GreaterThanOne;

  private final int LessThanTen;

  private final List<String> MyUniqueList;

  private final List<ComplexListElement> MyComplexUniqueList;

  private final String MyUtf8Bytes;

  private final List<String> MyListOfUtf8Bytes;

  protected GetConstraintsInput(BuilderImpl builder) {
    this.MyString = builder.MyString();
    this.NonEmptyString = builder.NonEmptyString();
    this.StringLessThanOrEqualToTen = builder.StringLessThanOrEqualToTen();
    this.MyBlob = builder.MyBlob();
    this.NonEmptyBlob = builder.NonEmptyBlob();
    this.BlobLessThanOrEqualToTen = builder.BlobLessThanOrEqualToTen();
    this.MyList = builder.MyList();
    this.NonEmptyList = builder.NonEmptyList();
    this.ListLessThanOrEqualToTen = builder.ListLessThanOrEqualToTen();
    this.MyMap = builder.MyMap();
    this.NonEmptyMap = builder.NonEmptyMap();
    this.MapLessThanOrEqualToTen = builder.MapLessThanOrEqualToTen();
    this.Alphabetic = builder.Alphabetic();
    this.OneToTen = builder.OneToTen();
    this.GreaterThanOne = builder.GreaterThanOne();
    this.LessThanTen = builder.LessThanTen();
    this.MyUniqueList = builder.MyUniqueList();
    this.MyComplexUniqueList = builder.MyComplexUniqueList();
    this.MyUtf8Bytes = builder.MyUtf8Bytes();
    this.MyListOfUtf8Bytes = builder.MyListOfUtf8Bytes();
  }

  public String MyString() {
    return this.MyString;
  }

  public String NonEmptyString() {
    return this.NonEmptyString;
  }

  public String StringLessThanOrEqualToTen() {
    return this.StringLessThanOrEqualToTen;
  }

  public ByteBuffer MyBlob() {
    return this.MyBlob;
  }

  public ByteBuffer NonEmptyBlob() {
    return this.NonEmptyBlob;
  }

  public ByteBuffer BlobLessThanOrEqualToTen() {
    return this.BlobLessThanOrEqualToTen;
  }

  public List<String> MyList() {
    return this.MyList;
  }

  public List<String> NonEmptyList() {
    return this.NonEmptyList;
  }

  public List<String> ListLessThanOrEqualToTen() {
    return this.ListLessThanOrEqualToTen;
  }

  public Map<String, String> MyMap() {
    return this.MyMap;
  }

  public Map<String, String> NonEmptyMap() {
    return this.NonEmptyMap;
  }

  public Map<String, String> MapLessThanOrEqualToTen() {
    return this.MapLessThanOrEqualToTen;
  }

  public String Alphabetic() {
    return this.Alphabetic;
  }

  public int OneToTen() {
    return this.OneToTen;
  }

  public int GreaterThanOne() {
    return this.GreaterThanOne;
  }

  public int LessThanTen() {
    return this.LessThanTen;
  }

  public List<String> MyUniqueList() {
    return this.MyUniqueList;
  }

  public List<ComplexListElement> MyComplexUniqueList() {
    return this.MyComplexUniqueList;
  }

  public String MyUtf8Bytes() {
    return this.MyUtf8Bytes;
  }

  public List<String> MyListOfUtf8Bytes() {
    return this.MyListOfUtf8Bytes;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder MyString(String MyString);

    String MyString();

    Builder NonEmptyString(String NonEmptyString);

    String NonEmptyString();

    Builder StringLessThanOrEqualToTen(String StringLessThanOrEqualToTen);

    String StringLessThanOrEqualToTen();

    Builder MyBlob(ByteBuffer MyBlob);

    ByteBuffer MyBlob();

    Builder NonEmptyBlob(ByteBuffer NonEmptyBlob);

    ByteBuffer NonEmptyBlob();

    Builder BlobLessThanOrEqualToTen(ByteBuffer BlobLessThanOrEqualToTen);

    ByteBuffer BlobLessThanOrEqualToTen();

    Builder MyList(List<String> MyList);

    List<String> MyList();

    Builder NonEmptyList(List<String> NonEmptyList);

    List<String> NonEmptyList();

    Builder ListLessThanOrEqualToTen(List<String> ListLessThanOrEqualToTen);

    List<String> ListLessThanOrEqualToTen();

    Builder MyMap(Map<String, String> MyMap);

    Map<String, String> MyMap();

    Builder NonEmptyMap(Map<String, String> NonEmptyMap);

    Map<String, String> NonEmptyMap();

    Builder MapLessThanOrEqualToTen(Map<String, String> MapLessThanOrEqualToTen);

    Map<String, String> MapLessThanOrEqualToTen();

    Builder Alphabetic(String Alphabetic);

    String Alphabetic();

    Builder OneToTen(int OneToTen);

    int OneToTen();

    Builder GreaterThanOne(int GreaterThanOne);

    int GreaterThanOne();

    Builder LessThanTen(int LessThanTen);

    int LessThanTen();

    Builder MyUniqueList(List<String> MyUniqueList);

    List<String> MyUniqueList();

    Builder MyComplexUniqueList(List<ComplexListElement> MyComplexUniqueList);

    List<ComplexListElement> MyComplexUniqueList();

    Builder MyUtf8Bytes(String MyUtf8Bytes);

    String MyUtf8Bytes();

    Builder MyListOfUtf8Bytes(List<String> MyListOfUtf8Bytes);

    List<String> MyListOfUtf8Bytes();

    GetConstraintsInput build();
  }

  static class BuilderImpl implements Builder {
    protected String MyString;

    protected String NonEmptyString;

    protected String StringLessThanOrEqualToTen;

    protected ByteBuffer MyBlob;

    protected ByteBuffer NonEmptyBlob;

    protected ByteBuffer BlobLessThanOrEqualToTen;

    protected List<String> MyList;

    protected List<String> NonEmptyList;

    protected List<String> ListLessThanOrEqualToTen;

    protected Map<String, String> MyMap;

    protected Map<String, String> NonEmptyMap;

    protected Map<String, String> MapLessThanOrEqualToTen;

    protected String Alphabetic;

    protected int OneToTen;

    protected int GreaterThanOne;

    protected int LessThanTen;

    protected List<String> MyUniqueList;

    protected List<ComplexListElement> MyComplexUniqueList;

    protected String MyUtf8Bytes;

    protected List<String> MyListOfUtf8Bytes;

    protected BuilderImpl() {
    }

    protected BuilderImpl(GetConstraintsInput model) {
      this.MyString = model.MyString();
      this.NonEmptyString = model.NonEmptyString();
      this.StringLessThanOrEqualToTen = model.StringLessThanOrEqualToTen();
      this.MyBlob = model.MyBlob();
      this.NonEmptyBlob = model.NonEmptyBlob();
      this.BlobLessThanOrEqualToTen = model.BlobLessThanOrEqualToTen();
      this.MyList = model.MyList();
      this.NonEmptyList = model.NonEmptyList();
      this.ListLessThanOrEqualToTen = model.ListLessThanOrEqualToTen();
      this.MyMap = model.MyMap();
      this.NonEmptyMap = model.NonEmptyMap();
      this.MapLessThanOrEqualToTen = model.MapLessThanOrEqualToTen();
      this.Alphabetic = model.Alphabetic();
      this.OneToTen = model.OneToTen();
      this.GreaterThanOne = model.GreaterThanOne();
      this.LessThanTen = model.LessThanTen();
      this.MyUniqueList = model.MyUniqueList();
      this.MyComplexUniqueList = model.MyComplexUniqueList();
      this.MyUtf8Bytes = model.MyUtf8Bytes();
      this.MyListOfUtf8Bytes = model.MyListOfUtf8Bytes();
    }

    public Builder MyString(String MyString) {
      this.MyString = MyString;
      return this;
    }

    public String MyString() {
      return this.MyString;
    }

    public Builder NonEmptyString(String NonEmptyString) {
      this.NonEmptyString = NonEmptyString;
      return this;
    }

    public String NonEmptyString() {
      return this.NonEmptyString;
    }

    public Builder StringLessThanOrEqualToTen(String StringLessThanOrEqualToTen) {
      this.StringLessThanOrEqualToTen = StringLessThanOrEqualToTen;
      return this;
    }

    public String StringLessThanOrEqualToTen() {
      return this.StringLessThanOrEqualToTen;
    }

    public Builder MyBlob(ByteBuffer MyBlob) {
      this.MyBlob = MyBlob;
      return this;
    }

    public ByteBuffer MyBlob() {
      return this.MyBlob;
    }

    public Builder NonEmptyBlob(ByteBuffer NonEmptyBlob) {
      this.NonEmptyBlob = NonEmptyBlob;
      return this;
    }

    public ByteBuffer NonEmptyBlob() {
      return this.NonEmptyBlob;
    }

    public Builder BlobLessThanOrEqualToTen(ByteBuffer BlobLessThanOrEqualToTen) {
      this.BlobLessThanOrEqualToTen = BlobLessThanOrEqualToTen;
      return this;
    }

    public ByteBuffer BlobLessThanOrEqualToTen() {
      return this.BlobLessThanOrEqualToTen;
    }

    public Builder MyList(List<String> MyList) {
      this.MyList = MyList;
      return this;
    }

    public List<String> MyList() {
      return this.MyList;
    }

    public Builder NonEmptyList(List<String> NonEmptyList) {
      this.NonEmptyList = NonEmptyList;
      return this;
    }

    public List<String> NonEmptyList() {
      return this.NonEmptyList;
    }

    public Builder ListLessThanOrEqualToTen(List<String> ListLessThanOrEqualToTen) {
      this.ListLessThanOrEqualToTen = ListLessThanOrEqualToTen;
      return this;
    }

    public List<String> ListLessThanOrEqualToTen() {
      return this.ListLessThanOrEqualToTen;
    }

    public Builder MyMap(Map<String, String> MyMap) {
      this.MyMap = MyMap;
      return this;
    }

    public Map<String, String> MyMap() {
      return this.MyMap;
    }

    public Builder NonEmptyMap(Map<String, String> NonEmptyMap) {
      this.NonEmptyMap = NonEmptyMap;
      return this;
    }

    public Map<String, String> NonEmptyMap() {
      return this.NonEmptyMap;
    }

    public Builder MapLessThanOrEqualToTen(Map<String, String> MapLessThanOrEqualToTen) {
      this.MapLessThanOrEqualToTen = MapLessThanOrEqualToTen;
      return this;
    }

    public Map<String, String> MapLessThanOrEqualToTen() {
      return this.MapLessThanOrEqualToTen;
    }

    public Builder Alphabetic(String Alphabetic) {
      this.Alphabetic = Alphabetic;
      return this;
    }

    public String Alphabetic() {
      return this.Alphabetic;
    }

    public Builder OneToTen(int OneToTen) {
      this.OneToTen = OneToTen;
      return this;
    }

    public int OneToTen() {
      return this.OneToTen;
    }

    public Builder GreaterThanOne(int GreaterThanOne) {
      this.GreaterThanOne = GreaterThanOne;
      return this;
    }

    public int GreaterThanOne() {
      return this.GreaterThanOne;
    }

    public Builder LessThanTen(int LessThanTen) {
      this.LessThanTen = LessThanTen;
      return this;
    }

    public int LessThanTen() {
      return this.LessThanTen;
    }

    public Builder MyUniqueList(List<String> MyUniqueList) {
      this.MyUniqueList = MyUniqueList;
      return this;
    }

    public List<String> MyUniqueList() {
      return this.MyUniqueList;
    }

    public Builder MyComplexUniqueList(List<ComplexListElement> MyComplexUniqueList) {
      this.MyComplexUniqueList = MyComplexUniqueList;
      return this;
    }

    public List<ComplexListElement> MyComplexUniqueList() {
      return this.MyComplexUniqueList;
    }

    public Builder MyUtf8Bytes(String MyUtf8Bytes) {
      this.MyUtf8Bytes = MyUtf8Bytes;
      return this;
    }

    public String MyUtf8Bytes() {
      return this.MyUtf8Bytes;
    }

    public Builder MyListOfUtf8Bytes(List<String> MyListOfUtf8Bytes) {
      this.MyListOfUtf8Bytes = MyListOfUtf8Bytes;
      return this;
    }

    public List<String> MyListOfUtf8Bytes() {
      return this.MyListOfUtf8Bytes;
    }

    public GetConstraintsInput build() {
      if (Objects.nonNull(this.MyString()) && this.MyString().length() < 1) {
        throw new IllegalArgumentException("The size of `MyString` must be greater than or equal to 1");
      }
      if (Objects.nonNull(this.MyString()) && this.MyString().length() > 10) {
        throw new IllegalArgumentException("The size of `MyString` must be less than or equal to 10");
      }
      if (Objects.nonNull(this.NonEmptyString()) && this.NonEmptyString().length() < 1) {
        throw new IllegalArgumentException("The size of `NonEmptyString` must be greater than or equal to 1");
      }
      if (Objects.nonNull(this.StringLessThanOrEqualToTen()) && this.StringLessThanOrEqualToTen().length() > 10) {
        throw new IllegalArgumentException("The size of `StringLessThanOrEqualToTen` must be less than or equal to 10");
      }
      if (Objects.nonNull(this.MyBlob()) && this.MyBlob().remaining() < 1) {
        throw new IllegalArgumentException("The size of `MyBlob` must be greater than or equal to 1");
      }
      if (Objects.nonNull(this.MyBlob()) && this.MyBlob().remaining() > 10) {
        throw new IllegalArgumentException("The size of `MyBlob` must be less than or equal to 10");
      }
      if (Objects.nonNull(this.NonEmptyBlob()) && this.NonEmptyBlob().remaining() < 1) {
        throw new IllegalArgumentException("The size of `NonEmptyBlob` must be greater than or equal to 1");
      }
      if (Objects.nonNull(this.BlobLessThanOrEqualToTen()) && this.BlobLessThanOrEqualToTen().remaining() > 10) {
        throw new IllegalArgumentException("The size of `BlobLessThanOrEqualToTen` must be less than or equal to 10");
      }
      if (Objects.nonNull(this.MyList()) && this.MyList().size() < 1) {
        throw new IllegalArgumentException("The size of `MyList` must be greater than or equal to 1");
      }
      if (Objects.nonNull(this.MyList()) && this.MyList().size() > 10) {
        throw new IllegalArgumentException("The size of `MyList` must be less than or equal to 10");
      }
      if (Objects.nonNull(this.NonEmptyList()) && this.NonEmptyList().size() < 1) {
        throw new IllegalArgumentException("The size of `NonEmptyList` must be greater than or equal to 1");
      }
      if (Objects.nonNull(this.ListLessThanOrEqualToTen()) && this.ListLessThanOrEqualToTen().size() > 10) {
        throw new IllegalArgumentException("The size of `ListLessThanOrEqualToTen` must be less than or equal to 10");
      }
      if (Objects.nonNull(this.MyMap()) && this.MyMap().size() < 1) {
        throw new IllegalArgumentException("The size of `MyMap` must be greater than or equal to 1");
      }
      if (Objects.nonNull(this.MyMap()) && this.MyMap().size() > 10) {
        throw new IllegalArgumentException("The size of `MyMap` must be less than or equal to 10");
      }
      if (Objects.nonNull(this.NonEmptyMap()) && this.NonEmptyMap().size() < 1) {
        throw new IllegalArgumentException("The size of `NonEmptyMap` must be greater than or equal to 1");
      }
      if (Objects.nonNull(this.MapLessThanOrEqualToTen()) && this.MapLessThanOrEqualToTen().size() > 10) {
        throw new IllegalArgumentException("The size of `MapLessThanOrEqualToTen` must be less than or equal to 10");
      }
      if (Objects.nonNull(this.OneToTen()) && this.OneToTen() < 1) {
        throw new IllegalArgumentException("`OneToTen` must be greater than or equal to 1");
      }
      if (Objects.nonNull(this.OneToTen()) && this.OneToTen() > 10) {
        throw new IllegalArgumentException("`OneToTen` must be less than or equal to 10.");
      }
      if (Objects.nonNull(this.GreaterThanOne()) && this.GreaterThanOne() < 1) {
        throw new IllegalArgumentException("`GreaterThanOne` must be greater than or equal to 1");
      }
      if (Objects.nonNull(this.LessThanTen()) && this.LessThanTen() > 10) {
        throw new IllegalArgumentException("`LessThanTen` must be less than or equal to 10.");
      }
      return new GetConstraintsInput(this);
    }
  }
}
