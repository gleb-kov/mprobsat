#ifndef MPROBSAT_BIT_VECTOR_H
#define MPROBSAT_BIT_VECTOR_H

#include <vector>
#include <cstdint>
#include <climits>
#include <cassert>

constexpr uint64_t MostSignificantBitCT(uint64_t x) {
    return x > 1 ? 1 + MostSignificantBitCT(x >> 1) : 0;
}

template<typename TWord>
struct TBitSeqTraits {
    static constexpr uint8_t NumBits = CHAR_BIT * sizeof(TWord);
    static constexpr TWord ModMask = static_cast<TWord>(NumBits - 1);
    static constexpr TWord DivShift = MostSignificantBitCT(NumBits);

    static_assert(std::is_unsigned<TWord>::value, "Expected std::is_unsigned<T>::value.");
    static_assert((NumBits & (NumBits - 1)) == 0, "NumBits should be a power of 2.");

    static inline constexpr TWord BitMask(uint8_t pos) {
        return TWord(1) << pos;
    }
};

template<typename T = uint64_t>
class TBitVector {
public:
    using TWord = T;
    using TTraits = TBitSeqTraits<TWord>;

private:
    uint64_t Size_;
    std::vector<TWord> Data_;

public:
    TBitVector()
            : Size_(0), Data_(0) {
    }

    explicit TBitVector(uint64_t size)
            : Size_(size), Data_(static_cast<size_t>((Size_ + TTraits::ModMask) >> TTraits::DivShift), 0) {
    }

    ~TBitVector() = default;

    void Resize(uint64_t size) {
        Size_ = size;
        Data_.resize((Size_ + TTraits::ModMask) >> TTraits::DivShift);
    }

    bool Set(uint64_t pos) {
        assert(pos < Size_);
        TWord &val = Data_[pos >> TTraits::DivShift];
        if (val & TTraits::BitMask(pos & TTraits::ModMask))
            return false;
        val |= TTraits::BitMask(pos & TTraits::ModMask);
        return true;
    }

    [[nodiscard]] bool Test(uint64_t pos) const {
        assert(pos < Size_);
        return Data_[pos >> TTraits::DivShift] & BitMask(pos & TTraits::ModMask);
    }

    void Reset(uint64_t pos) {
        assert(pos < Size_);
        Data_[pos >> TTraits::DivShift] &= ~TTraits::BitMask(pos & TTraits::ModMask);
    }

    void Revert(uint64_t pos) {
        assert(pos < Size_);
        Data_[pos >> TTraits::DivShift] ^= TTraits::BitMask(pos & TTraits::ModMask);
    }

    [[nodiscard]] size_t Count() const {
        size_t count = 0;
        for (size_t i = 0; i < Data_.size(); ++i) {
            count += (size_t) PopCount(Data_[i]);
        }
        return count;
    }

    const TWord *Data() const {
        return Data_.data();
    }
};

#endif //MPROBSAT_BIT_VECTOR_H
