#ifndef MPROBSAT_BIT_VECTOR_H
#define MPROBSAT_BIT_VECTOR_H

#include <vector>
#include <cstdint>
#include <climits>
#include <cassert>
#include <random>

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

class TBitVector {
public:
    using TWord = uint64_t;
    using TTraits = TBitSeqTraits<TWord>;

public:
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

    void FillRandom(std::mt19937 &dev) {
        static std::uniform_int_distribution<uint64_t> distr(0, std::numeric_limits<uint64_t>::max());
        for (uint64_t &elem : Data_) {
            elem = distr(dev);
        }
    }

    [[nodiscard]] bool Test(uint64_t pos) const {
        assert(pos < Size_);
        return Data_[pos >> TTraits::DivShift] & TTraits::BitMask(pos & TTraits::ModMask);
    }

    void Reset(uint64_t pos) {
        assert(pos < Size_);
        Data_[pos >> TTraits::DivShift] &= ~TTraits::BitMask(pos & TTraits::ModMask);
    }

    void Revert(uint64_t pos) {
        assert(pos < Size_);
        Data_[pos >> TTraits::DivShift] ^= TTraits::BitMask(pos & TTraits::ModMask);
    }

    [[nodiscard]] const TWord *Data() const {
        return Data_.data();
    }

private:
    uint64_t Size_;
    std::vector<TWord> Data_;
};

#endif //MPROBSAT_BIT_VECTOR_H
